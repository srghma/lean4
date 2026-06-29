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
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [116, 101, 114, 109, 105, 110, 97, 108, 84, 97, 99, 116, 105, 99, 115, 65, 115, 83, 111, 114, 114, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16213016488940853032 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10944533187742096104 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<139> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 139, m_capacity: 139, m_length: 138, m_data: [119, 104, 101, 110, 32, 101, 110, 97, 98, 108, 101, 100, 44, 32, 116, 101, 114, 109, 105, 110, 97, 108, 32, 116, 97, 99, 116, 105, 99, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 103, 114, 105, 110, 100, 96, 32, 97, 110, 100, 32, 96, 111, 109, 101, 103, 97, 96, 32, 97, 114, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 111, 114, 114, 121, 96, 46, 32, 85, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 97, 110, 100, 32, 102, 105, 120, 105, 110, 103, 32, 98, 111, 111, 116, 115, 116, 114, 97, 112, 112, 105, 110, 103, 32, 105, 115, 115, 117, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11456239060754360645 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3200922834059057545 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_debug_terminalTacticsAsSorry: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkTacticExMsg___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkTacticExMsg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkTacticExMsg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkTacticExMsg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkTacticExMsg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkTacticExMsg___closed__2_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkTacticExMsg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkTacticExMsg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkTacticExMsg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkTacticExMsg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkTacticExMsg___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_mkTacticExMsg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkTacticExMsg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkTacticExMsg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkTacticExMsg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_throwTacticEx___redArg___closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_throwTacticEx___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwTacticEx___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_throwTacticEx___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_throwTacticEx___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9884631923193754313 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
pub static l_Lean_MVarId_checkNotAssigned___closed__0_value: crate::leanh::LeanStringObject<49> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_checkNotAssigned___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_checkNotAssigned___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_checkNotAssigned___closed__2_value: crate::leanh::LeanStringObject<70> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_checkNotAssigned___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_checkNotAssigned___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_checkNotAssigned___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_checkNotAssigned___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_checkNotAssigned___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_checkNotAssigned___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,142734480563613395 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15847151208953044930 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1826193737664319561 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14998221293048064268 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2824242023938616461 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4283501524993450821 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14927488885235163468 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17596233699544133669 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9760373788854647792 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2995894122792280700 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4482773431925144505 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12438958728964694155 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1901113268 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9603354042393261625 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16753743204010399146 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13532387658210436566 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,4161607161240432151 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_admit___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_admit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_admit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_admit___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_admit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4924044685138168346 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_admit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_admit___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_isFVar___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_getNondepPropHyps___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_getNondepPropHyps___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_getNondepPropHyps___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_getNondepPropHyps___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_getNondepPropHyps___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_getNondepPropHyps___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_getNondepPropHyps___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_getNondepPropHyps___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_inferInstance___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    50,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        96, 105, 110, 102, 101, 114, 95, 105, 110, 115, 116, 97, 110, 99, 101, 96, 32, 116, 97, 99,
        116, 105, 99, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 115, 115, 105, 103,
        110, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_MVarId_inferInstance___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_inferInstance___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_inferInstance___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_inferInstance___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_inferInstance___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_inferInstance___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_inferInstance___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_inferInstance___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_inferInstance___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_inferInstance___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_inferInstance___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_inferInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5120837411420157255 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_inferInstance___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_isSubsingleton___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_isSubsingleton___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_isSubsingleton___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_isSubsingleton___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_isSubsingleton___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13409365605382521367 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_isSubsingleton___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_isSubsingleton___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [115, 107, 105, 112, 65, 115, 115, 105, 103, 110, 101, 100, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16145843736367156323 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5414973503309327526 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<113> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 113, m_capacity: 113, m_length: 112, m_data: [105, 110, 32, 116, 104, 101, 32, 96, 114, 119, 96, 32, 97, 110, 100, 32, 96, 115, 105, 109, 112, 96, 32, 116, 97, 99, 116, 105, 99, 115, 44, 32, 105, 102, 32, 97, 110, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 105, 115, 32, 97, 115, 115, 105, 103, 110, 101, 100, 44, 32, 100, 111, 32, 110, 111, 116, 32, 116, 114, 121, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9078769453211668998 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9140867362275919303 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_tactic_skipAssignedInstances: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(
    mut v_name_3789_: *mut crate::leanh::LeanObject,
    mut v_decl_3790_: *mut crate::leanh::LeanObject,
    mut v_ref_3791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut v_unused_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3793_ = crate::leanh::lean_ctor_get(v_decl_3790_, 0);
                v_descr_3794_ = crate::leanh::lean_ctor_get(v_decl_3790_, 1);
                v_deprecation_x3f_3795_ = crate::leanh::lean_ctor_get(v_decl_3790_, 2);
                v___x_3796_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3797_ = (crate::leanh::lean_unbox(v_defValue_3793_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_3796_, 0 as u32, v___x_3797_);
                crate::leanh::lean_inc(v_deprecation_x3f_3795_);
                crate::leanh::lean_inc_ref(v_descr_3794_);
                crate::leanh::lean_inc_n(v_name_3789_, 2);
                v___x_3798_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3798_, 0, v_name_3789_);
                crate::leanh::lean_ctor_set(v___x_3798_, 1, v_ref_3791_);
                crate::leanh::lean_ctor_set(v___x_3798_, 2, v___x_3796_);
                crate::leanh::lean_ctor_set(v___x_3798_, 3, v_descr_3794_);
                crate::leanh::lean_ctor_set(v___x_3798_, 4, v_deprecation_x3f_3795_);
                v___x_3799_ = lean_register_option(v_name_3789_, v___x_3798_);
                if crate::leanh::lean_obj_tag(v___x_3799_) == 0 {
                    v_isSharedCheck_3807_ = (!crate::leanh::lean_is_exclusive(v___x_3799_)) as u8;
                    if v_isSharedCheck_3807_ == 0 {
                        v_unused_3808_ = crate::leanh::lean_ctor_get(v___x_3799_, 0);
                        crate::leanh::lean_dec(v_unused_3808_);
                        v___x_3801_ = v___x_3799_;
                        v_isShared_3802_ = v_isSharedCheck_3807_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3799_);
                        v___x_3801_ = crate::leanh::lean_box(0);
                        v_isShared_3802_ = v_isSharedCheck_3807_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3789_);
                    v_a_3809_ = crate::leanh::lean_ctor_get(v___x_3799_, 0);
                    v_isSharedCheck_3816_ = (!crate::leanh::lean_is_exclusive(v___x_3799_)) as u8;
                    if v_isSharedCheck_3816_ == 0 {
                        v___x_3811_ = v___x_3799_;
                        v_isShared_3812_ = v_isSharedCheck_3816_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3809_);
                        crate::leanh::lean_dec(v___x_3799_);
                        v___x_3811_ = crate::leanh::lean_box(0);
                        v_isShared_3812_ = v_isSharedCheck_3816_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3793_);
                v___x_3803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3803_, 0, v_name_3789_);
                crate::leanh::lean_ctor_set(v___x_3803_, 1, v_defValue_3793_);
                if v_isShared_3802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3801_, 0, v___x_3803_);
                    v___x_3805_ = v___x_3801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
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
                    v_reuseFailAlloc_3815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
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
    mut v_name_3817_: *mut crate::leanh::LeanObject,
    mut v_decl_3818_: *mut crate::leanh::LeanObject,
    mut v_ref_3819_: *mut crate::leanh::LeanObject,
    mut v_a_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_3817_, v_decl_3818_, v_ref_3819_);
    crate::leanh::lean_dec_ref(v_decl_3818_);
    return v_res_3821_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_;
    v___x_3842_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_;
    v___x_3843_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_;
    v___x_3844_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3841_, v___x_3842_, v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(
    mut v_a_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3846_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
    return v_res_3846_;
}
pub unsafe fn l_Lean_MVarId_getTag(
    mut v_mvarId_3847_: *mut crate::leanh::LeanObject,
    mut v_a_3848_: *mut crate::leanh::LeanObject,
    mut v_a_3849_: *mut crate::leanh::LeanObject,
    mut v_a_3850_: *mut crate::leanh::LeanObject,
    mut v_a_3851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v_userName_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut v_a_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_3853_) == 0 {
                    v_a_3854_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
                    v_isSharedCheck_3862_ = (!crate::leanh::lean_is_exclusive(v___x_3853_)) as u8;
                    if v_isSharedCheck_3862_ == 0 {
                        v___x_3856_ = v___x_3853_;
                        v_isShared_3857_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3854_);
                        crate::leanh::lean_dec(v___x_3853_);
                        v___x_3856_ = crate::leanh::lean_box(0);
                        v_isShared_3857_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3863_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
                    v_isSharedCheck_3870_ = (!crate::leanh::lean_is_exclusive(v___x_3853_)) as u8;
                    if v_isSharedCheck_3870_ == 0 {
                        v___x_3865_ = v___x_3853_;
                        v_isShared_3866_ = v_isSharedCheck_3870_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3863_);
                        crate::leanh::lean_dec(v___x_3853_);
                        v___x_3865_ = crate::leanh::lean_box(0);
                        v_isShared_3866_ = v_isSharedCheck_3870_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_userName_3858_ = crate::leanh::lean_ctor_get(v_a_3854_, 0);
                crate::leanh::lean_inc(v_userName_3858_);
                crate::leanh::lean_dec(v_a_3854_);
                if v_isShared_3857_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3856_, 0, v_userName_3858_);
                    v___x_3860_ = v___x_3856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_userName_3858_);
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
                    v_reuseFailAlloc_3869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
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
    mut v_mvarId_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_a_3875_: *mut crate::leanh::LeanObject,
    mut v_a_3876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3877_ = l_Lean_MVarId_getTag(v_mvarId_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
    crate::leanh::lean_dec(v_a_3875_);
    crate::leanh::lean_dec_ref(v_a_3874_);
    crate::leanh::lean_dec(v_a_3873_);
    crate::leanh::lean_dec_ref(v_a_3872_);
    return v_res_3877_;
}
pub unsafe fn l_Lean_MVarId_setTag___redArg(
    mut v_mvarId_3878_: *mut crate::leanh::LeanObject,
    mut v_tag_3879_: *mut crate::leanh::LeanObject,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3890_: u8 = 0;
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3882_ = lean_st_ref_take(v_a_3880_);
                v_mctx_3883_ = crate::leanh::lean_ctor_get(v___x_3882_, 0);
                v_cache_3884_ = crate::leanh::lean_ctor_get(v___x_3882_, 1);
                v_zetaDeltaFVarIds_3885_ = crate::leanh::lean_ctor_get(v___x_3882_, 2);
                v_postponed_3886_ = crate::leanh::lean_ctor_get(v___x_3882_, 3);
                v_diag_3887_ = crate::leanh::lean_ctor_get(v___x_3882_, 4);
                v_isSharedCheck_3898_ = (!crate::leanh::lean_is_exclusive(v___x_3882_)) as u8;
                if v_isSharedCheck_3898_ == 0 {
                    v___x_3889_ = v___x_3882_;
                    v_isShared_3890_ = v_isSharedCheck_3898_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3887_);
                    crate::leanh::lean_inc(v_postponed_3886_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3885_);
                    crate::leanh::lean_inc(v_cache_3884_);
                    crate::leanh::lean_inc(v_mctx_3883_);
                    crate::leanh::lean_dec(v___x_3882_);
                    v___x_3889_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3889_, 0, v___x_3891_);
                    v___x_3893_ = v___x_3889_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_cache_3884_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3897_,
                        2,
                        v_zetaDeltaFVarIds_3885_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 3, v_postponed_3886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 4, v_diag_3887_);
                    v___x_3893_ = v_reuseFailAlloc_3897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3894_ = lean_st_ref_set(v_a_3880_, v___x_3893_);
                v___x_3895_ = crate::leanh::lean_box(0);
                v___x_3896_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3896_, 0, v___x_3895_);
                return v___x_3896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_setTag___redArg___boxed(
    mut v_mvarId_3899_: *mut crate::leanh::LeanObject,
    mut v_tag_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Lean_MVarId_setTag___redArg(v_mvarId_3899_, v_tag_3900_, v_a_3901_);
    crate::leanh::lean_dec(v_a_3901_);
    return v_res_3903_;
}
pub unsafe fn l_Lean_MVarId_setTag(
    mut v_mvarId_3904_: *mut crate::leanh::LeanObject,
    mut v_tag_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_a_3907_: *mut crate::leanh::LeanObject,
    mut v_a_3908_: *mut crate::leanh::LeanObject,
    mut v_a_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3911_ = l_Lean_MVarId_setTag___redArg(v_mvarId_3904_, v_tag_3905_, v_a_3907_);
    return v___x_3911_;
}
pub unsafe fn l_Lean_MVarId_setTag___boxed(
    mut v_mvarId_3912_: *mut crate::leanh::LeanObject,
    mut v_tag_3913_: *mut crate::leanh::LeanObject,
    mut v_a_3914_: *mut crate::leanh::LeanObject,
    mut v_a_3915_: *mut crate::leanh::LeanObject,
    mut v_a_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
    mut v_a_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Lean_MVarId_setTag(
        v_mvarId_3912_,
        v_tag_3913_,
        v_a_3914_,
        v_a_3915_,
        v_a_3916_,
        v_a_3917_,
    );
    crate::leanh::lean_dec(v_a_3917_);
    crate::leanh::lean_dec_ref(v_a_3916_);
    crate::leanh::lean_dec(v_a_3915_);
    crate::leanh::lean_dec_ref(v_a_3914_);
    return v_res_3919_;
}
pub unsafe fn l_Lean_Meta_appendTag___lam__0(
    mut v_suffix_3920_: *mut crate::leanh::LeanObject,
    mut v_x_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3922_ = lean_erase_macro_scopes(v_suffix_3920_);
    v___x_3923_ = l_Lean_Name_append(v_x_3921_, v___x_3922_);
    return v___x_3923_;
}
pub unsafe fn l_Lean_Meta_appendTag(
    mut v_tag_3924_: *mut crate::leanh::LeanObject,
    mut v_suffix_3925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_view_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3935_: u8 = 0;
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v_name_3929_ = crate::leanh::lean_ctor_get(v_view_3928_, 0);
                    v_imported_3930_ = crate::leanh::lean_ctor_get(v_view_3928_, 1);
                    v_ctx_3931_ = crate::leanh::lean_ctor_get(v_view_3928_, 2);
                    v_scopes_3932_ = crate::leanh::lean_ctor_get(v_view_3928_, 3);
                    v_isSharedCheck_3941_ = (!crate::leanh::lean_is_exclusive(v_view_3928_)) as u8;
                    if v_isSharedCheck_3941_ == 0 {
                        v___x_3934_ = v_view_3928_;
                        v_isShared_3935_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_scopes_3932_);
                        crate::leanh::lean_inc(v_ctx_3931_);
                        crate::leanh::lean_inc(v_imported_3930_);
                        crate::leanh::lean_inc(v_name_3929_);
                        crate::leanh::lean_dec(v_view_3928_);
                        v___x_3934_ = crate::leanh::lean_box(0);
                        v_isShared_3935_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3936_ = l_Lean_Meta_appendTag___lam__0(v_suffix_3925_, v_name_3929_);
                if v_isShared_3935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3934_, 0, v___x_3936_);
                    v___x_3938_ = v___x_3934_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3940_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_imported_3930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_ctx_3931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_scopes_3932_);
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
    mut v_mvarId_3942_: *mut crate::leanh::LeanObject,
    mut v_suffix_3943_: *mut crate::leanh::LeanObject,
    mut v_a_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_a_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3942_);
                v___x_3949_ = l_Lean_MVarId_getTag(
                    v_mvarId_3942_,
                    v_a_3944_,
                    v_a_3945_,
                    v_a_3946_,
                    v_a_3947_,
                );
                if crate::leanh::lean_obj_tag(v___x_3949_) == 0 {
                    v_a_3950_ = crate::leanh::lean_ctor_get(v___x_3949_, 0);
                    crate::leanh::lean_inc(v_a_3950_);
                    crate::leanh::lean_dec_ref_known(v___x_3949_, 1);
                    v___x_3951_ = l_Lean_Meta_appendTag(v_a_3950_, v_suffix_3943_);
                    v___x_3952_ =
                        l_Lean_MVarId_setTag___redArg(v_mvarId_3942_, v___x_3951_, v_a_3945_);
                    return v___x_3952_;
                } else {
                    crate::leanh::lean_dec(v_suffix_3943_);
                    crate::leanh::lean_dec(v_mvarId_3942_);
                    v_a_3953_ = crate::leanh::lean_ctor_get(v___x_3949_, 0);
                    v_isSharedCheck_3960_ = (!crate::leanh::lean_is_exclusive(v___x_3949_)) as u8;
                    if v_isSharedCheck_3960_ == 0 {
                        v___x_3955_ = v___x_3949_;
                        v_isShared_3956_ = v_isSharedCheck_3960_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3953_);
                        crate::leanh::lean_dec(v___x_3949_);
                        v___x_3955_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
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
    mut v_mvarId_3961_: *mut crate::leanh::LeanObject,
    mut v_suffix_3962_: *mut crate::leanh::LeanObject,
    mut v_a_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
    mut v_a_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3968_ = l_Lean_Meta_appendTagSuffix(
        v_mvarId_3961_,
        v_suffix_3962_,
        v_a_3963_,
        v_a_3964_,
        v_a_3965_,
        v_a_3966_,
    );
    crate::leanh::lean_dec(v_a_3966_);
    crate::leanh::lean_dec_ref(v_a_3965_);
    crate::leanh::lean_dec(v_a_3964_);
    crate::leanh::lean_dec_ref(v_a_3963_);
    return v_res_3968_;
}
pub unsafe fn l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
    mut v_type_3969_: *mut crate::leanh::LeanObject,
    mut v_tag_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
    mut v_a_3972_: *mut crate::leanh::LeanObject,
    mut v_a_3973_: *mut crate::leanh::LeanObject,
    mut v_a_3974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3976_, 0, v_type_3969_);
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
    mut v_type_3979_: *mut crate::leanh::LeanObject,
    mut v_tag_3980_: *mut crate::leanh::LeanObject,
    mut v_a_3981_: *mut crate::leanh::LeanObject,
    mut v_a_3982_: *mut crate::leanh::LeanObject,
    mut v_a_3983_: *mut crate::leanh::LeanObject,
    mut v_a_3984_: *mut crate::leanh::LeanObject,
    mut v_a_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
        v_type_3979_,
        v_tag_3980_,
        v_a_3981_,
        v_a_3982_,
        v_a_3983_,
        v_a_3984_,
    );
    crate::leanh::lean_dec(v_a_3984_);
    crate::leanh::lean_dec_ref(v_a_3983_);
    crate::leanh::lean_dec(v_a_3982_);
    crate::leanh::lean_dec_ref(v_a_3981_);
    return v_res_3986_;
}
pub unsafe fn _init_l_Lean_Meta_mkTacticExMsg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_Meta_mkTacticExMsg___closed__0;
    v___x_3989_ = l_Lean_stringToMessageData(v___x_3988_);
    return v___x_3989_;
}
pub unsafe fn _init_l_Lean_Meta_mkTacticExMsg___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3991_ = l_Lean_Meta_mkTacticExMsg___closed__2;
    v___x_3992_ = l_Lean_stringToMessageData(v___x_3991_);
    return v___x_3992_;
}
pub unsafe fn _init_l_Lean_Meta_mkTacticExMsg___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3994_ = l_Lean_Meta_mkTacticExMsg___closed__4;
    v___x_3995_ = l_Lean_stringToMessageData(v___x_3994_);
    return v___x_3995_;
}
pub unsafe fn l_Lean_Meta_mkTacticExMsg(
    mut v_tacticName_3996_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3997_: *mut crate::leanh::LeanObject,
    mut v_msg_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3999_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__1,
    );
    v___x_4000_ = l_Lean_MessageData_ofName(v_tacticName_3996_);
    v___x_4001_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4001_, 0, v___x_3999_);
    crate::leanh::lean_ctor_set(v___x_4001_, 1, v___x_4000_);
    v___x_4002_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__3_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__3,
    );
    v___x_4003_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4003_, 0, v___x_4001_);
    crate::leanh::lean_ctor_set(v___x_4003_, 1, v___x_4002_);
    v___x_4004_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4004_, 0, v___x_4003_);
    crate::leanh::lean_ctor_set(v___x_4004_, 1, v_msg_3998_);
    v___x_4005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__5_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__5,
    );
    v___x_4006_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4006_, 0, v___x_4004_);
    crate::leanh::lean_ctor_set(v___x_4006_, 1, v___x_4005_);
    v___x_4007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4007_, 0, v_mvarId_3997_);
    v___x_4008_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4008_, 0, v___x_4006_);
    crate::leanh::lean_ctor_set(v___x_4008_, 1, v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(
    mut v_msgData_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4015_ = lean_st_ref_get(v___y_4013_);
    v_env_4016_ = crate::leanh::lean_ctor_get(v___x_4015_, 0);
    crate::leanh::lean_inc_ref(v_env_4016_);
    crate::leanh::lean_dec(v___x_4015_);
    v___x_4017_ = lean_st_ref_get(v___y_4011_);
    v_mctx_4018_ = crate::leanh::lean_ctor_get(v___x_4017_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4018_);
    crate::leanh::lean_dec(v___x_4017_);
    v_lctx_4019_ = crate::leanh::lean_ctor_get(v___y_4010_, 2);
    v_options_4020_ = crate::leanh::lean_ctor_get(v___y_4012_, 2);
    crate::leanh::lean_inc_ref(v_options_4020_);
    crate::leanh::lean_inc_ref(v_lctx_4019_);
    v___x_4021_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4021_, 0, v_env_4016_);
    crate::leanh::lean_ctor_set(v___x_4021_, 1, v_mctx_4018_);
    crate::leanh::lean_ctor_set(v___x_4021_, 2, v_lctx_4019_);
    crate::leanh::lean_ctor_set(v___x_4021_, 3, v_options_4020_);
    v___x_4022_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4022_, 0, v___x_4021_);
    crate::leanh::lean_ctor_set(v___x_4022_, 1, v_msgData_4009_);
    v___x_4023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4023_, 0, v___x_4022_);
    return v___x_4023_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(
    mut v_msgData_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
    mut v___y_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4030_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
    crate::leanh::lean_dec(v___y_4028_);
    crate::leanh::lean_dec_ref(v___y_4027_);
    crate::leanh::lean_dec(v___y_4026_);
    crate::leanh::lean_dec_ref(v___y_4025_);
    return v_res_4030_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
    mut v_msg_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4042_: u8 = 0;
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4037_ = crate::leanh::lean_ctor_get(v___y_4034_, 5);
                v___x_4038_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
                v_a_4039_ = crate::leanh::lean_ctor_get(v___x_4038_, 0);
                v_isSharedCheck_4047_ = (!crate::leanh::lean_is_exclusive(v___x_4038_)) as u8;
                if v_isSharedCheck_4047_ == 0 {
                    v___x_4041_ = v___x_4038_;
                    v_isShared_4042_ = v_isSharedCheck_4047_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4039_);
                    crate::leanh::lean_dec(v___x_4038_);
                    v___x_4041_ = crate::leanh::lean_box(0);
                    v_isShared_4042_ = v_isSharedCheck_4047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4037_);
                v___x_4043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4043_, 0, v_ref_4037_);
                crate::leanh::lean_ctor_set(v___x_4043_, 1, v_a_4039_);
                if v_isShared_4042_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4041_, 1);
                    crate::leanh::lean_ctor_set(v___x_4041_, 0, v___x_4043_);
                    v___x_4045_ = v___x_4041_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4043_);
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
    mut v_msg_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4054_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
        v_msg_4048_,
        v___y_4049_,
        v___y_4050_,
        v___y_4051_,
        v___y_4052_,
    );
    crate::leanh::lean_dec(v___y_4052_);
    crate::leanh::lean_dec_ref(v___y_4051_);
    crate::leanh::lean_dec(v___y_4050_);
    crate::leanh::lean_dec_ref(v___y_4049_);
    return v_res_4054_;
}
pub unsafe fn _init_l_Lean_Meta_throwTacticEx___redArg___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Lean_Meta_throwTacticEx___redArg___closed__0;
    v___x_4057_ = l_Lean_stringToMessageData(v___x_4056_);
    return v___x_4057_;
}
pub unsafe fn l_Lean_Meta_throwTacticEx___redArg(
    mut v_tacticName_4058_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4059_: *mut crate::leanh::LeanObject,
    mut v_msg_x3f_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
    mut v_a_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_msg_x3f_4060_) == 0 {
        let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4066_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1_once),
            _init_l_Lean_Meta_mkTacticExMsg___closed__1,
        );
        v___x_4067_ = l_Lean_MessageData_ofName(v_tacticName_4058_);
        v___x_4068_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4068_, 0, v___x_4066_);
        crate::leanh::lean_ctor_set(v___x_4068_, 1, v___x_4067_);
        v___x_4069_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_throwTacticEx___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_throwTacticEx___redArg___closed__1_once),
            _init_l_Lean_Meta_throwTacticEx___redArg___closed__1,
        );
        v___x_4070_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4070_, 0, v___x_4068_);
        crate::leanh::lean_ctor_set(v___x_4070_, 1, v___x_4069_);
        v___x_4071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4071_, 0, v_mvarId_4059_);
        v___x_4072_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4072_, 0, v___x_4070_);
        crate::leanh::lean_ctor_set(v___x_4072_, 1, v___x_4071_);
        v___x_4073_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
            v___x_4072_,
            v_a_4061_,
            v_a_4062_,
            v_a_4063_,
            v_a_4064_,
        );
        return v___x_4073_;
    } else {
        let mut v_val_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4074_ = crate::leanh::lean_ctor_get(v_msg_x3f_4060_, 0);
        crate::leanh::lean_inc(v_val_4074_);
        crate::leanh::lean_dec_ref_known(v_msg_x3f_4060_, 1);
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
    mut v_tacticName_4077_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4078_: *mut crate::leanh::LeanObject,
    mut v_msg_x3f_4079_: *mut crate::leanh::LeanObject,
    mut v_a_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_Lean_Meta_throwTacticEx___redArg(
        v_tacticName_4077_,
        v_mvarId_4078_,
        v_msg_x3f_4079_,
        v_a_4080_,
        v_a_4081_,
        v_a_4082_,
        v_a_4083_,
    );
    crate::leanh::lean_dec(v_a_4083_);
    crate::leanh::lean_dec_ref(v_a_4082_);
    crate::leanh::lean_dec(v_a_4081_);
    crate::leanh::lean_dec_ref(v_a_4080_);
    return v_res_4085_;
}
pub unsafe fn l_Lean_Meta_throwTacticEx(
    mut v_00_u03b1_4086_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4087_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4088_: *mut crate::leanh::LeanObject,
    mut v_msg_x3f_4089_: *mut crate::leanh::LeanObject,
    mut v_a_4090_: *mut crate::leanh::LeanObject,
    mut v_a_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
    mut v_a_4093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4096_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4097_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4098_: *mut crate::leanh::LeanObject,
    mut v_msg_x3f_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_a_4103_: *mut crate::leanh::LeanObject,
    mut v_a_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4103_);
    crate::leanh::lean_dec_ref(v_a_4102_);
    crate::leanh::lean_dec(v_a_4101_);
    crate::leanh::lean_dec_ref(v_a_4100_);
    return v_res_4105_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(
    mut v_00_u03b1_4106_: *mut crate::leanh::LeanObject,
    mut v_msg_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4114_: *mut crate::leanh::LeanObject,
    mut v_msg_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(
        v_00_u03b1_4114_,
        v_msg_4115_,
        v___y_4116_,
        v___y_4117_,
        v___y_4118_,
        v___y_4119_,
    );
    crate::leanh::lean_dec(v___y_4119_);
    crate::leanh::lean_dec_ref(v___y_4118_);
    crate::leanh::lean_dec(v___y_4117_);
    crate::leanh::lean_dec_ref(v___y_4116_);
    return v_res_4121_;
}
pub unsafe fn _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4123_ = l_Lean_Meta_throwNestedTacticEx___redArg___closed__0;
    v___x_4124_ = l_Lean_stringToMessageData(v___x_4123_);
    return v___x_4124_;
}
pub unsafe fn l_Lean_Meta_throwNestedTacticEx___redArg(
    mut v_tacticName_4128_: *mut crate::leanh::LeanObject,
    mut v_ex_4129_: *mut crate::leanh::LeanObject,
    mut v_a_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
    mut v_a_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nestedMsg_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: u8 = 0;
    v_nestedMsg_4135_ = l_Lean_Exception_toMessageData(v_ex_4129_);
    v___x_4136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__1,
    );
    v___x_4137_ = l_Lean_MessageData_ofName(v_tacticName_4128_);
    v___x_4138_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4136_);
    crate::leanh::lean_ctor_set(v___x_4138_, 1, v___x_4137_);
    v___x_4139_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once),
        _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1,
    );
    v___x_4140_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4140_, 0, v___x_4138_);
    crate::leanh::lean_ctor_set(v___x_4140_, 1, v___x_4139_);
    crate::leanh::lean_inc_ref(v_nestedMsg_4135_);
    v_msg_4141_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_msg_4141_, 0, v___x_4140_);
    crate::leanh::lean_ctor_set(v_msg_4141_, 1, v_nestedMsg_4135_);
    v_kind_4142_ = l_Lean_MessageData_kind(v_nestedMsg_4135_);
    crate::leanh::lean_dec_ref(v_nestedMsg_4135_);
    v___x_4143_ = l_Lean_Name_isAnonymous(v_kind_4142_);
    if v___x_4143_ == 0 {
        let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4144_ = l_Lean_Meta_throwNestedTacticEx___redArg___closed__3;
        v___x_4145_ = l_Lean_Name_append(v___x_4144_, v_kind_4142_);
        v___x_4146_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4146_, 0, v___x_4145_);
        crate::leanh::lean_ctor_set(v___x_4146_, 1, v_msg_4141_);
        v___x_4147_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
            v___x_4146_,
            v_a_4130_,
            v_a_4131_,
            v_a_4132_,
            v_a_4133_,
        );
        return v___x_4147_;
    } else {
        let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_kind_4142_);
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
    mut v_tacticName_4149_: *mut crate::leanh::LeanObject,
    mut v_ex_4150_: *mut crate::leanh::LeanObject,
    mut v_a_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
    mut v_a_4154_: *mut crate::leanh::LeanObject,
    mut v_a_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4156_ = l_Lean_Meta_throwNestedTacticEx___redArg(
        v_tacticName_4149_,
        v_ex_4150_,
        v_a_4151_,
        v_a_4152_,
        v_a_4153_,
        v_a_4154_,
    );
    crate::leanh::lean_dec(v_a_4154_);
    crate::leanh::lean_dec_ref(v_a_4153_);
    crate::leanh::lean_dec(v_a_4152_);
    crate::leanh::lean_dec_ref(v_a_4151_);
    return v_res_4156_;
}
pub unsafe fn l_Lean_Meta_throwNestedTacticEx(
    mut v_00_u03b1_4157_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4158_: *mut crate::leanh::LeanObject,
    mut v_ex_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4166_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4167_: *mut crate::leanh::LeanObject,
    mut v_ex_4168_: *mut crate::leanh::LeanObject,
    mut v_a_4169_: *mut crate::leanh::LeanObject,
    mut v_a_4170_: *mut crate::leanh::LeanObject,
    mut v_a_4171_: *mut crate::leanh::LeanObject,
    mut v_a_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4174_ = l_Lean_Meta_throwNestedTacticEx(
        v_00_u03b1_4166_,
        v_tacticName_4167_,
        v_ex_4168_,
        v_a_4169_,
        v_a_4170_,
        v_a_4171_,
        v_a_4172_,
    );
    crate::leanh::lean_dec(v_a_4172_);
    crate::leanh::lean_dec_ref(v_a_4171_);
    crate::leanh::lean_dec(v_a_4170_);
    crate::leanh::lean_dec_ref(v_a_4169_);
    return v_res_4174_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_keys_4175_: *mut crate::leanh::LeanObject,
    mut v_i_4176_: *mut crate::leanh::LeanObject,
    mut v_k_4177_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: u8 = 0;
    let mut v_k_x27_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4178_ = lean_array_get_size(v_keys_4175_);
                v___x_4179_ = lean_nat_dec_lt(v_i_4176_, v___x_4178_);
                if v___x_4179_ == 0 {
                    crate::leanh::lean_dec(v_i_4176_);
                    return v___x_4179_;
                } else {
                    v_k_x27_4180_ = lean_array_fget_borrowed(v_keys_4175_, v_i_4176_);
                    v___x_4181_ = l_Lean_instBEqMVarId_beq(v_k_4177_, v_k_x27_4180_);
                    if v___x_4181_ == 0 {
                        v___x_4182_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4183_ = lean_nat_add(v_i_4176_, v___x_4182_);
                        crate::leanh::lean_dec(v_i_4176_);
                        v_i_4176_ = v___x_4183_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4176_);
                        return v___x_4181_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_keys_4185_: *mut crate::leanh::LeanObject,
    mut v_i_4186_: *mut crate::leanh::LeanObject,
    mut v_k_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4188_: u8 = 0;
    let mut v_r_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4185_, v_i_4186_, v_k_4187_);
    crate::leanh::lean_dec(v_k_4187_);
    crate::leanh::lean_dec_ref(v_keys_4185_);
    v_r_4189_ = crate::leanh::lean_box((v_res_4188_) as usize);
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
    v___x_4194_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_4195_ = lean_usize_sub(v___x_4194_, v___x_4193_);
    return v___x_4195_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(
    mut v_x_4196_: *mut crate::leanh::LeanObject,
    mut v_x_4197_: usize,
    mut v_x_4198_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: usize = 0;
    let mut v___x_4202_: usize = 0;
    let mut v___x_4203_: usize = 0;
    let mut v_j_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: u8 = 0;
    let mut v_node_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: usize = 0;
    let mut v___x_4211_: u8 = 0;
    let mut v_ks_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4196_) == 0 {
                    v_es_4199_ = crate::leanh::lean_ctor_get(v_x_4196_, 0);
                    v___x_4200_ = crate::leanh::lean_box(2);
                    v___x_4201_ = 5usize;
                    v___x_4202_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4203_ = lean_usize_land(v_x_4197_, v___x_4202_);
                    v_j_4204_ = lean_usize_to_nat(v___x_4203_);
                    v___x_4205_ = lean_array_get_borrowed(v___x_4200_, v_es_4199_, v_j_4204_);
                    crate::leanh::lean_dec(v_j_4204_);
                    match crate::leanh::lean_obj_tag(v___x_4205_) {
                        0 => {
                            v_key_4206_ = crate::leanh::lean_ctor_get(v___x_4205_, 0);
                            v___x_4207_ = l_Lean_instBEqMVarId_beq(v_x_4198_, v_key_4206_);
                            return v___x_4207_;
                        }
                        1 => {
                            v_node_4208_ = crate::leanh::lean_ctor_get(v___x_4205_, 0);
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
                    v_ks_4212_ = crate::leanh::lean_ctor_get(v_x_4196_, 0);
                    v___x_4213_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4214_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4212_, v___x_4213_, v_x_4198_);
                    return v___x_4214_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4215_: *mut crate::leanh::LeanObject,
    mut v_x_4216_: *mut crate::leanh::LeanObject,
    mut v_x_4217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_596__boxed_4218_: usize = 0;
    let mut v_res_4219_: u8 = 0;
    let mut v_r_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_596__boxed_4218_ = crate::leanh::lean_unbox_usize(v_x_4216_);
    crate::leanh::lean_dec(v_x_4216_);
    v_res_4219_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_4215_, v_x_596__boxed_4218_, v_x_4217_);
    crate::leanh::lean_dec(v_x_4217_);
    crate::leanh::lean_dec_ref(v_x_4215_);
    v_r_4220_ = crate::leanh::lean_box((v_res_4219_) as usize);
    return v_r_4220_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(
    mut v_x_4221_: *mut crate::leanh::LeanObject,
    mut v_x_4222_: *mut crate::leanh::LeanObject,
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
    mut v_x_4226_: *mut crate::leanh::LeanObject,
    mut v_x_4227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4228_: u8 = 0;
    let mut v_r_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4228_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_4226_, v_x_4227_);
    crate::leanh::lean_dec(v_x_4227_);
    crate::leanh::lean_dec_ref(v_x_4226_);
    v_r_4229_ = crate::leanh::lean_box((v_res_4228_) as usize);
    return v_r_4229_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(
    mut v_mvarId_4230_: *mut crate::leanh::LeanObject,
    mut v___y_4231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = lean_st_ref_get(v___y_4231_);
    v_mctx_4234_ = crate::leanh::lean_ctor_get(v___x_4233_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4234_);
    crate::leanh::lean_dec(v___x_4233_);
    v_eAssignment_4235_ = crate::leanh::lean_ctor_get(v_mctx_4234_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_4235_);
    crate::leanh::lean_dec_ref(v_mctx_4234_);
    v___x_4236_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_4235_, v_mvarId_4230_);
    crate::leanh::lean_dec_ref(v_eAssignment_4235_);
    v___x_4237_ = crate::leanh::lean_box((v___x_4236_) as usize);
    v___x_4238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4238_, 0, v___x_4237_);
    return v___x_4238_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(
    mut v_mvarId_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
    mut v___y_4241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4242_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(
        v_mvarId_4239_,
        v___y_4240_,
    );
    crate::leanh::lean_dec(v___y_4240_);
    crate::leanh::lean_dec(v_mvarId_4239_);
    return v_res_4242_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4244_ = l_Lean_MVarId_checkNotAssigned___closed__0;
    v___x_4245_ = l_Lean_stringToMessageData(v___x_4244_);
    return v___x_4245_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_MVarId_checkNotAssigned___closed__3;
    v___x_4250_ = l_Lean_MessageData_ofFormat(v___x_4249_);
    return v___x_4250_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__4),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__4_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__4,
    );
    v___x_4252_ = l_Lean_MessageData_note(v___x_4251_);
    return v___x_4252_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4253_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__5),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__5_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__5,
    );
    v___x_4254_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__1_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__1,
    );
    v___x_4255_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4255_, 0, v___x_4254_);
    crate::leanh::lean_ctor_set(v___x_4255_, 1, v___x_4253_);
    return v___x_4255_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4256_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__6),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__6_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__6,
    );
    v___x_4257_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4257_, 0, v___x_4256_);
    return v___x_4257_;
}
pub unsafe fn l_Lean_MVarId_checkNotAssigned(
    mut v_mvarId_4258_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4269_: u8 = 0;
    let mut v___x_4270_: u8 = 0;
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_a_4266_ = crate::leanh::lean_ctor_get(v___x_4265_, 0);
                v_isSharedCheck_4277_ = (!crate::leanh::lean_is_exclusive(v___x_4265_)) as u8;
                if v_isSharedCheck_4277_ == 0 {
                    v___x_4268_ = v___x_4265_;
                    v_isShared_4269_ = v_isSharedCheck_4277_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4266_);
                    crate::leanh::lean_dec(v___x_4265_);
                    v___x_4268_ = crate::leanh::lean_box(0);
                    v_isShared_4269_ = v_isSharedCheck_4277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4270_ = (crate::leanh::lean_unbox(v_a_4266_) as u8);
                crate::leanh::lean_dec(v_a_4266_);
                if v___x_4270_ == 0 {
                    crate::leanh::lean_dec(v_tacticName_4259_);
                    crate::leanh::lean_dec(v_mvarId_4258_);
                    v___x_4271_ = crate::leanh::lean_box(0);
                    if v_isShared_4269_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4268_, 0, v___x_4271_);
                        v___x_4273_ = v___x_4268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
                        v___x_4273_ = v_reuseFailAlloc_4274_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4268_);
                    v___x_4275_ = crate::leanh::lean_obj_once(
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
    mut v_mvarId_4278_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4279_: *mut crate::leanh::LeanObject,
    mut v_a_4280_: *mut crate::leanh::LeanObject,
    mut v_a_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: *mut crate::leanh::LeanObject,
    mut v_a_4283_: *mut crate::leanh::LeanObject,
    mut v_a_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4285_ = l_Lean_MVarId_checkNotAssigned(
        v_mvarId_4278_,
        v_tacticName_4279_,
        v_a_4280_,
        v_a_4281_,
        v_a_4282_,
        v_a_4283_,
    );
    crate::leanh::lean_dec(v_a_4283_);
    crate::leanh::lean_dec_ref(v_a_4282_);
    crate::leanh::lean_dec(v_a_4281_);
    crate::leanh::lean_dec_ref(v_a_4280_);
    return v_res_4285_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(
    mut v_mvarId_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(
        v_mvarId_4286_,
        v___y_4288_,
    );
    return v___x_4292_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(
    mut v_mvarId_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4299_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(
        v_mvarId_4293_,
        v___y_4294_,
        v___y_4295_,
        v___y_4296_,
        v___y_4297_,
    );
    crate::leanh::lean_dec(v___y_4297_);
    crate::leanh::lean_dec_ref(v___y_4296_);
    crate::leanh::lean_dec(v___y_4295_);
    crate::leanh::lean_dec_ref(v___y_4294_);
    crate::leanh::lean_dec(v_mvarId_4293_);
    return v_res_4299_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(
    mut v_00_u03b2_4300_: *mut crate::leanh::LeanObject,
    mut v_x_4301_: *mut crate::leanh::LeanObject,
    mut v_x_4302_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4303_: u8 = 0;
    v___x_4303_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_4301_, v_x_4302_);
    return v___x_4303_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(
    mut v_00_u03b2_4304_: *mut crate::leanh::LeanObject,
    mut v_x_4305_: *mut crate::leanh::LeanObject,
    mut v_x_4306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4307_: u8 = 0;
    let mut v_r_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4307_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_4304_, v_x_4305_, v_x_4306_);
    crate::leanh::lean_dec(v_x_4306_);
    crate::leanh::lean_dec_ref(v_x_4305_);
    v_r_4308_ = crate::leanh::lean_box((v_res_4307_) as usize);
    return v_r_4308_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4309_: *mut crate::leanh::LeanObject,
    mut v_x_4310_: *mut crate::leanh::LeanObject,
    mut v_x_4311_: usize,
    mut v_x_4312_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4313_: u8 = 0;
    v___x_4313_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_4310_, v_x_4311_, v_x_4312_);
    return v___x_4313_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4314_: *mut crate::leanh::LeanObject,
    mut v_x_4315_: *mut crate::leanh::LeanObject,
    mut v_x_4316_: *mut crate::leanh::LeanObject,
    mut v_x_4317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_769__boxed_4318_: usize = 0;
    let mut v_res_4319_: u8 = 0;
    let mut v_r_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_769__boxed_4318_ = crate::leanh::lean_unbox_usize(v_x_4316_);
    crate::leanh::lean_dec(v_x_4316_);
    v_res_4319_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_4314_, v_x_4315_, v_x_769__boxed_4318_, v_x_4317_);
    crate::leanh::lean_dec(v_x_4317_);
    crate::leanh::lean_dec_ref(v_x_4315_);
    v_r_4320_ = crate::leanh::lean_box((v_res_4319_) as usize);
    return v_r_4320_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4321_: *mut crate::leanh::LeanObject,
    mut v_keys_4322_: *mut crate::leanh::LeanObject,
    mut v_vals_4323_: *mut crate::leanh::LeanObject,
    mut v_heq_4324_: *mut crate::leanh::LeanObject,
    mut v_i_4325_: *mut crate::leanh::LeanObject,
    mut v_k_4326_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4327_: u8 = 0;
    v___x_4327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4322_, v_i_4325_, v_k_4326_);
    return v___x_4327_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4328_: *mut crate::leanh::LeanObject,
    mut v_keys_4329_: *mut crate::leanh::LeanObject,
    mut v_vals_4330_: *mut crate::leanh::LeanObject,
    mut v_heq_4331_: *mut crate::leanh::LeanObject,
    mut v_i_4332_: *mut crate::leanh::LeanObject,
    mut v_k_4333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4334_: u8 = 0;
    let mut v_r_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4334_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4328_, v_keys_4329_, v_vals_4330_, v_heq_4331_, v_i_4332_, v_k_4333_);
    crate::leanh::lean_dec(v_k_4333_);
    crate::leanh::lean_dec_ref(v_vals_4330_);
    crate::leanh::lean_dec_ref(v_keys_4329_);
    v_r_4335_ = crate::leanh::lean_box((v_res_4334_) as usize);
    return v_r_4335_;
}
pub unsafe fn l_Lean_MVarId_getType(
    mut v_mvarId_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v_type_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4351_: u8 = 0;
    let mut v_a_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_4342_) == 0 {
                    v_a_4343_ = crate::leanh::lean_ctor_get(v___x_4342_, 0);
                    v_isSharedCheck_4351_ = (!crate::leanh::lean_is_exclusive(v___x_4342_)) as u8;
                    if v_isSharedCheck_4351_ == 0 {
                        v___x_4345_ = v___x_4342_;
                        v_isShared_4346_ = v_isSharedCheck_4351_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4343_);
                        crate::leanh::lean_dec(v___x_4342_);
                        v___x_4345_ = crate::leanh::lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4351_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4352_ = crate::leanh::lean_ctor_get(v___x_4342_, 0);
                    v_isSharedCheck_4359_ = (!crate::leanh::lean_is_exclusive(v___x_4342_)) as u8;
                    if v_isSharedCheck_4359_ == 0 {
                        v___x_4354_ = v___x_4342_;
                        v_isShared_4355_ = v_isSharedCheck_4359_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4352_);
                        crate::leanh::lean_dec(v___x_4342_);
                        v___x_4354_ = crate::leanh::lean_box(0);
                        v_isShared_4355_ = v_isSharedCheck_4359_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_type_4347_ = crate::leanh::lean_ctor_get(v_a_4343_, 2);
                crate::leanh::lean_inc_ref(v_type_4347_);
                crate::leanh::lean_dec(v_a_4343_);
                if v_isShared_4346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4345_, 0, v_type_4347_);
                    v___x_4349_ = v___x_4345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_type_4347_);
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
                    v_reuseFailAlloc_4358_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
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
    mut v_mvarId_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Lean_MVarId_getType(v_mvarId_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_);
    crate::leanh::lean_dec(v_a_4364_);
    crate::leanh::lean_dec_ref(v_a_4363_);
    crate::leanh::lean_dec(v_a_4362_);
    crate::leanh::lean_dec_ref(v_a_4361_);
    return v_res_4366_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
    mut v_e_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut v_unused_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4370_ = l_Lean_Expr_hasMVar(v_e_4367_);
                if v___x_4370_ == 0 {
                    v___x_4371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4371_, 0, v_e_4367_);
                    return v___x_4371_;
                } else {
                    v___x_4372_ = lean_st_ref_get(v___y_4368_);
                    v_mctx_4373_ = crate::leanh::lean_ctor_get(v___x_4372_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4373_);
                    crate::leanh::lean_dec(v___x_4372_);
                    v___x_4374_ = l_Lean_instantiateMVarsCore(v_mctx_4373_, v_e_4367_);
                    v_fst_4375_ = crate::leanh::lean_ctor_get(v___x_4374_, 0);
                    crate::leanh::lean_inc(v_fst_4375_);
                    v_snd_4376_ = crate::leanh::lean_ctor_get(v___x_4374_, 1);
                    crate::leanh::lean_inc(v_snd_4376_);
                    crate::leanh::lean_dec_ref(v___x_4374_);
                    v___x_4377_ = lean_st_ref_take(v___y_4368_);
                    v_cache_4378_ = crate::leanh::lean_ctor_get(v___x_4377_, 1);
                    v_zetaDeltaFVarIds_4379_ = crate::leanh::lean_ctor_get(v___x_4377_, 2);
                    v_postponed_4380_ = crate::leanh::lean_ctor_get(v___x_4377_, 3);
                    v_diag_4381_ = crate::leanh::lean_ctor_get(v___x_4377_, 4);
                    v_isSharedCheck_4390_ = (!crate::leanh::lean_is_exclusive(v___x_4377_)) as u8;
                    if v_isSharedCheck_4390_ == 0 {
                        v_unused_4391_ = crate::leanh::lean_ctor_get(v___x_4377_, 0);
                        crate::leanh::lean_dec(v_unused_4391_);
                        v___x_4383_ = v___x_4377_;
                        v_isShared_4384_ = v_isSharedCheck_4390_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4381_);
                        crate::leanh::lean_inc(v_postponed_4380_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4379_);
                        crate::leanh::lean_inc(v_cache_4378_);
                        crate::leanh::lean_dec(v___x_4377_);
                        v___x_4383_ = crate::leanh::lean_box(0);
                        v_isShared_4384_ = v_isSharedCheck_4390_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4384_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4383_, 0, v_snd_4376_);
                    v___x_4386_ = v___x_4383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_snd_4376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_cache_4378_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4389_,
                        2,
                        v_zetaDeltaFVarIds_4379_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 3, v_postponed_4380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 4, v_diag_4381_);
                    v___x_4386_ = v_reuseFailAlloc_4389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4387_ = lean_st_ref_set(v___y_4368_, v___x_4386_);
                v___x_4388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4388_, 0, v_fst_4375_);
                return v___x_4388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(
    mut v_e_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4395_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
        v_e_4392_,
        v___y_4393_,
    );
    crate::leanh::lean_dec(v___y_4393_);
    return v_res_4395_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(
    mut v_e_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4402_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
        v_e_4396_,
        v___y_4398_,
    );
    return v___x_4402_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(
    mut v_e_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v___y_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(
        v_e_4403_,
        v___y_4404_,
        v___y_4405_,
        v___y_4406_,
        v___y_4407_,
    );
    crate::leanh::lean_dec(v___y_4407_);
    crate::leanh::lean_dec_ref(v___y_4406_);
    crate::leanh::lean_dec(v___y_4405_);
    crate::leanh::lean_dec_ref(v___y_4404_);
    return v_res_4409_;
}
pub unsafe fn l_Lean_MVarId_getType_x27(
    mut v_mvarId_4410_: *mut crate::leanh::LeanObject,
    mut v_a_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
    mut v_a_4413_: *mut crate::leanh::LeanObject,
    mut v_a_4414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4416_ = l_Lean_MVarId_getType(v_mvarId_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
    if crate::leanh::lean_obj_tag(v___x_4416_) == 0 {
        let mut v_a_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4417_ = crate::leanh::lean_ctor_get(v___x_4416_, 0);
        crate::leanh::lean_inc(v_a_4417_);
        crate::leanh::lean_dec_ref_known(v___x_4416_, 1);
        crate::leanh::lean_inc(v_a_4414_);
        crate::leanh::lean_inc_ref(v_a_4413_);
        crate::leanh::lean_inc(v_a_4412_);
        crate::leanh::lean_inc_ref(v_a_4411_);
        v___x_4418_ = lean_whnf(v_a_4417_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
        if crate::leanh::lean_obj_tag(v___x_4418_) == 0 {
            let mut v_a_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_4419_ = crate::leanh::lean_ctor_get(v___x_4418_, 0);
            crate::leanh::lean_inc(v_a_4419_);
            crate::leanh::lean_dec_ref_known(v___x_4418_, 1);
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
    mut v_mvarId_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4427_ =
        l_Lean_MVarId_getType_x27(v_mvarId_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
    crate::leanh::lean_dec(v_a_4425_);
    crate::leanh::lean_dec_ref(v_a_4424_);
    crate::leanh::lean_dec(v_a_4423_);
    crate::leanh::lean_dec_ref(v_a_4422_);
    return v_res_4427_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4493_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_;
    v___x_4494_ = 0;
    v___x_4495_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_;
    v___x_4496_ = l_Lean_registerTraceClass(v___x_4493_, v___x_4494_, v___x_4495_);
    return v___x_4496_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(
    mut v_a_4497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4498_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
    return v_res_4498_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
    mut v_mvarId_4499_: *mut crate::leanh::LeanObject,
    mut v_x_4500_: *mut crate::leanh::LeanObject,
    mut v___y_4501_: *mut crate::leanh::LeanObject,
    mut v___y_4502_: *mut crate::leanh::LeanObject,
    mut v___y_4503_: *mut crate::leanh::LeanObject,
    mut v___y_4504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_a_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4506_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_4499_,
                    v_x_4500_,
                    v___y_4501_,
                    v___y_4502_,
                    v___y_4503_,
                    v___y_4504_,
                );
                if crate::leanh::lean_obj_tag(v___x_4506_) == 0 {
                    v_a_4507_ = crate::leanh::lean_ctor_get(v___x_4506_, 0);
                    v_isSharedCheck_4514_ = (!crate::leanh::lean_is_exclusive(v___x_4506_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4509_ = v___x_4506_;
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4507_);
                        crate::leanh::lean_dec(v___x_4506_);
                        v___x_4509_ = crate::leanh::lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4515_ = crate::leanh::lean_ctor_get(v___x_4506_, 0);
                    v_isSharedCheck_4522_ = (!crate::leanh::lean_is_exclusive(v___x_4506_)) as u8;
                    if v_isSharedCheck_4522_ == 0 {
                        v___x_4517_ = v___x_4506_;
                        v_isShared_4518_ = v_isSharedCheck_4522_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4515_);
                        crate::leanh::lean_dec(v___x_4506_);
                        v___x_4517_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
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
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
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
    mut v_mvarId_4523_: *mut crate::leanh::LeanObject,
    mut v_x_4524_: *mut crate::leanh::LeanObject,
    mut v___y_4525_: *mut crate::leanh::LeanObject,
    mut v___y_4526_: *mut crate::leanh::LeanObject,
    mut v___y_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4530_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
        v_mvarId_4523_,
        v_x_4524_,
        v___y_4525_,
        v___y_4526_,
        v___y_4527_,
        v___y_4528_,
    );
    crate::leanh::lean_dec(v___y_4528_);
    crate::leanh::lean_dec_ref(v___y_4527_);
    crate::leanh::lean_dec(v___y_4526_);
    crate::leanh::lean_dec_ref(v___y_4525_);
    return v_res_4530_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(
    mut v_00_u03b1_4531_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4532_: *mut crate::leanh::LeanObject,
    mut v_x_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4540_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4541_: *mut crate::leanh::LeanObject,
    mut v_x_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(
        v_00_u03b1_4540_,
        v_mvarId_4541_,
        v_x_4542_,
        v___y_4543_,
        v___y_4544_,
        v___y_4545_,
        v___y_4546_,
    );
    crate::leanh::lean_dec(v___y_4546_);
    crate::leanh::lean_dec_ref(v___y_4545_);
    crate::leanh::lean_dec(v___y_4544_);
    crate::leanh::lean_dec_ref(v___y_4543_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_4549_: *mut crate::leanh::LeanObject,
    mut v_x_4550_: *mut crate::leanh::LeanObject,
    mut v_x_4551_: *mut crate::leanh::LeanObject,
    mut v_x_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4557_: u8 = 0;
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4553_ = crate::leanh::lean_ctor_get(v_x_4549_, 0);
                v_vs_4554_ = crate::leanh::lean_ctor_get(v_x_4549_, 1);
                v_isSharedCheck_4578_ = (!crate::leanh::lean_is_exclusive(v_x_4549_)) as u8;
                if v_isSharedCheck_4578_ == 0 {
                    v___x_4556_ = v_x_4549_;
                    v_isShared_4557_ = v_isSharedCheck_4578_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4554_);
                    crate::leanh::lean_inc(v_ks_4553_);
                    crate::leanh::lean_dec(v_x_4549_);
                    v___x_4556_ = crate::leanh::lean_box(0);
                    v_isShared_4557_ = v_isSharedCheck_4578_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4558_ = lean_array_get_size(v_ks_4553_);
                v___x_4559_ = lean_nat_dec_lt(v_x_4550_, v___x_4558_);
                if v___x_4559_ == 0 {
                    crate::leanh::lean_dec(v_x_4550_);
                    v___x_4560_ = lean_array_push(v_ks_4553_, v_x_4551_);
                    v___x_4561_ = lean_array_push(v_vs_4554_, v_x_4552_);
                    if v_isShared_4557_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4556_, 1, v___x_4561_);
                        crate::leanh::lean_ctor_set(v___x_4556_, 0, v___x_4560_);
                        v___x_4563_ = v___x_4556_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4564_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4560_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 1, v___x_4561_);
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
                            v_reuseFailAlloc_4572_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_ks_4553_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_vs_4554_);
                            v___x_4568_ = v_reuseFailAlloc_4572_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4573_ = lean_array_fset(v_ks_4553_, v_x_4550_, v_x_4551_);
                        v___x_4574_ = lean_array_fset(v_vs_4554_, v_x_4550_, v_x_4552_);
                        crate::leanh::lean_dec(v_x_4550_);
                        if v_isShared_4557_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4556_, 1, v___x_4574_);
                            crate::leanh::lean_ctor_set(v___x_4556_, 0, v___x_4573_);
                            v___x_4576_ = v___x_4556_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4577_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4573_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4574_);
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
                v___x_4569_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4570_ = lean_nat_add(v_x_4550_, v___x_4569_);
                crate::leanh::lean_dec(v_x_4550_);
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
    mut v_n_4579_: *mut crate::leanh::LeanObject,
    mut v_k_4580_: *mut crate::leanh::LeanObject,
    mut v_v_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4583_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_4579_, v___x_4582_, v_k_4580_, v_v_4581_);
    return v___x_4583_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4584_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4584_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(
    mut v_x_4585_: *mut crate::leanh::LeanObject,
    mut v_x_4586_: usize,
    mut v_x_4587_: usize,
    mut v_x_4588_: *mut crate::leanh::LeanObject,
    mut v_x_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: usize = 0;
    let mut v___x_4592_: usize = 0;
    let mut v___x_4593_: usize = 0;
    let mut v___x_4594_: usize = 0;
    let mut v_j_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: u8 = 0;
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v_v_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v_node_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4625_: u8 = 0;
    let mut v___x_4626_: usize = 0;
    let mut v___x_4627_: usize = 0;
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4634_: u8 = 0;
    let mut v_unused_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4640_: u8 = 0;
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4645_: u8 = 0;
    let mut v_ks_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: usize = 0;
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: u8 = 0;
    let mut v_reuseFailAlloc_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4585_) == 0 {
                    v_es_4590_ = crate::leanh::lean_ctor_get(v_x_4585_, 0);
                    v___x_4591_ = 5usize;
                    v___x_4592_ = 1usize;
                    v___x_4593_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4594_ = lean_usize_land(v_x_4586_, v___x_4593_);
                    v_j_4595_ = lean_usize_to_nat(v___x_4594_);
                    v___x_4596_ = lean_array_get_size(v_es_4590_);
                    v___x_4597_ = lean_nat_dec_lt(v_j_4595_, v___x_4596_);
                    if v___x_4597_ == 0 {
                        crate::leanh::lean_dec(v_j_4595_);
                        crate::leanh::lean_dec(v_x_4589_);
                        crate::leanh::lean_dec(v_x_4588_);
                        return v_x_4585_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4590_);
                        v_isSharedCheck_4634_ = (!crate::leanh::lean_is_exclusive(v_x_4585_)) as u8;
                        if v_isSharedCheck_4634_ == 0 {
                            v_unused_4635_ = crate::leanh::lean_ctor_get(v_x_4585_, 0);
                            crate::leanh::lean_dec(v_unused_4635_);
                            v___x_4599_ = v_x_4585_;
                            v_isShared_4600_ = v_isSharedCheck_4634_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4585_);
                            v___x_4599_ = crate::leanh::lean_box(0);
                            v_isShared_4600_ = v_isSharedCheck_4634_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4636_ = crate::leanh::lean_ctor_get(v_x_4585_, 0);
                    v_vs_4637_ = crate::leanh::lean_ctor_get(v_x_4585_, 1);
                    v_isSharedCheck_4657_ = (!crate::leanh::lean_is_exclusive(v_x_4585_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4639_ = v_x_4585_;
                        v_isShared_4640_ = v_isSharedCheck_4657_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4637_);
                        crate::leanh::lean_inc(v_ks_4636_);
                        crate::leanh::lean_dec(v_x_4585_);
                        v___x_4639_ = crate::leanh::lean_box(0);
                        v_isShared_4640_ = v_isSharedCheck_4657_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4601_ = lean_array_fget(v_es_4590_, v_j_4595_);
                v___x_4602_ = crate::leanh::lean_box(0);
                v_xs_x27_4603_ = lean_array_fset(v_es_4590_, v_j_4595_, v___x_4602_);
                match crate::leanh::lean_obj_tag(v_v_4601_) {
                    0 => {
                        v_key_4610_ = crate::leanh::lean_ctor_get(v_v_4601_, 0);
                        v_val_4611_ = crate::leanh::lean_ctor_get(v_v_4601_, 1);
                        v_isSharedCheck_4621_ = (!crate::leanh::lean_is_exclusive(v_v_4601_)) as u8;
                        if v_isSharedCheck_4621_ == 0 {
                            v___x_4613_ = v_v_4601_;
                            v_isShared_4614_ = v_isSharedCheck_4621_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4611_);
                            crate::leanh::lean_inc(v_key_4610_);
                            crate::leanh::lean_dec(v_v_4601_);
                            v___x_4613_ = crate::leanh::lean_box(0);
                            v_isShared_4614_ = v_isSharedCheck_4621_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4622_ = crate::leanh::lean_ctor_get(v_v_4601_, 0);
                        v_isSharedCheck_4632_ = (!crate::leanh::lean_is_exclusive(v_v_4601_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4624_ = v_v_4601_;
                            v_isShared_4625_ = v_isSharedCheck_4632_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4622_);
                            crate::leanh::lean_dec(v_v_4601_);
                            v___x_4624_ = crate::leanh::lean_box(0);
                            v_isShared_4625_ = v_isSharedCheck_4632_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4633_, 0, v_x_4588_);
                        crate::leanh::lean_ctor_set(v___x_4633_, 1, v_x_4589_);
                        v___y_4605_ = v___x_4633_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4606_ = lean_array_fset(v_xs_x27_4603_, v_j_4595_, v___y_4605_);
                crate::leanh::lean_dec(v_j_4595_);
                if v_isShared_4600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4599_, 0, v___x_4606_);
                    v___x_4608_ = v___x_4599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
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
                    crate::leanh::lean_del_object(v___x_4613_);
                    v___x_4616_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4610_,
                        v_val_4611_,
                        v_x_4588_,
                        v_x_4589_,
                    );
                    v___x_4617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4617_, 0, v___x_4616_);
                    v___y_4605_ = v___x_4617_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4611_);
                    crate::leanh::lean_dec(v_key_4610_);
                    if v_isShared_4614_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4613_, 1, v_x_4589_);
                        crate::leanh::lean_ctor_set(v___x_4613_, 0, v_x_4588_);
                        v___x_4619_ = v___x_4613_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_x_4588_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_x_4589_);
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
                    crate::leanh::lean_ctor_set(v___x_4624_, 0, v___x_4628_);
                    v___x_4630_ = v___x_4624_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
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
                    v_reuseFailAlloc_4656_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_ks_4636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_vs_4637_);
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
                    v___x_4654_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4655_ = lean_nat_dec_lt(v___x_4653_, v___x_4654_);
                    crate::leanh::lean_dec(v___x_4653_);
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
                    v_ks_4646_ = crate::leanh::lean_ctor_get(v_newNode_4643_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4646_);
                    v_vs_4647_ = crate::leanh::lean_ctor_get(v_newNode_4643_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4647_);
                    crate::leanh::lean_dec_ref(v_newNode_4643_);
                    v___x_4648_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___x_4650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_4587_, v_ks_4646_, v_vs_4647_, v___x_4648_, v___x_4649_);
                    crate::leanh::lean_dec_ref(v_vs_4647_);
                    crate::leanh::lean_dec_ref(v_ks_4646_);
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
    mut v_keys_4659_: *mut crate::leanh::LeanObject,
    mut v_vals_4660_: *mut crate::leanh::LeanObject,
    mut v_i_4661_: *mut crate::leanh::LeanObject,
    mut v_entries_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: u8 = 0;
    let mut v_k_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: u64 = 0;
    let mut v_h_4668_: usize = 0;
    let mut v___x_4669_: usize = 0;
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: usize = 0;
    let mut v___x_4672_: usize = 0;
    let mut v___x_4673_: usize = 0;
    let mut v_h_4674_: usize = 0;
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4663_ = lean_array_get_size(v_keys_4659_);
                v___x_4664_ = lean_nat_dec_lt(v_i_4661_, v___x_4663_);
                if v___x_4664_ == 0 {
                    crate::leanh::lean_dec(v_i_4661_);
                    return v_entries_4662_;
                } else {
                    v_k_4665_ = lean_array_fget_borrowed(v_keys_4659_, v_i_4661_);
                    v_v_4666_ = lean_array_fget_borrowed(v_vals_4660_, v_i_4661_);
                    v___x_4667_ = l_Lean_instHashableMVarId_hash(v_k_4665_);
                    v_h_4668_ = lean_uint64_to_usize(v___x_4667_);
                    v___x_4669_ = 5usize;
                    v___x_4670_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4671_ = 1usize;
                    v___x_4672_ = lean_usize_sub(v_depth_4658_, v___x_4671_);
                    v___x_4673_ = lean_usize_mul(v___x_4669_, v___x_4672_);
                    v_h_4674_ = lean_usize_shift_right(v_h_4668_, v___x_4673_);
                    v___x_4675_ = lean_nat_add(v_i_4661_, v___x_4670_);
                    crate::leanh::lean_dec(v_i_4661_);
                    crate::leanh::lean_inc(v_v_4666_);
                    crate::leanh::lean_inc(v_k_4665_);
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
    mut v_depth_4678_: *mut crate::leanh::LeanObject,
    mut v_keys_4679_: *mut crate::leanh::LeanObject,
    mut v_vals_4680_: *mut crate::leanh::LeanObject,
    mut v_i_4681_: *mut crate::leanh::LeanObject,
    mut v_entries_4682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4683_: usize = 0;
    let mut v_res_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4683_ = crate::leanh::lean_unbox_usize(v_depth_4678_);
    crate::leanh::lean_dec(v_depth_4678_);
    v_res_4684_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_4683_, v_keys_4679_, v_vals_4680_, v_i_4681_, v_entries_4682_);
    crate::leanh::lean_dec_ref(v_vals_4680_);
    crate::leanh::lean_dec_ref(v_keys_4679_);
    return v_res_4684_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_4685_: *mut crate::leanh::LeanObject,
    mut v_x_4686_: *mut crate::leanh::LeanObject,
    mut v_x_4687_: *mut crate::leanh::LeanObject,
    mut v_x_4688_: *mut crate::leanh::LeanObject,
    mut v_x_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1015__boxed_4690_: usize = 0;
    let mut v_x_1016__boxed_4691_: usize = 0;
    let mut v_res_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1015__boxed_4690_ = crate::leanh::lean_unbox_usize(v_x_4686_);
    crate::leanh::lean_dec(v_x_4686_);
    v_x_1016__boxed_4691_ = crate::leanh::lean_unbox_usize(v_x_4687_);
    crate::leanh::lean_dec(v_x_4687_);
    v_res_4692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_4685_, v_x_1015__boxed_4690_, v_x_1016__boxed_4691_, v_x_4688_, v_x_4689_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(
    mut v_x_4693_: *mut crate::leanh::LeanObject,
    mut v_x_4694_: *mut crate::leanh::LeanObject,
    mut v_x_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4696_: u64 = 0;
    let mut v___x_4697_: usize = 0;
    let mut v___x_4698_: usize = 0;
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4696_ = l_Lean_instHashableMVarId_hash(v_x_4694_);
    v___x_4697_ = lean_uint64_to_usize(v___x_4696_);
    v___x_4698_ = 1usize;
    v___x_4699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_4693_, v___x_4697_, v___x_4698_, v_x_4694_, v_x_4695_);
    return v___x_4699_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
    mut v_mvarId_4700_: *mut crate::leanh::LeanObject,
    mut v_val_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4712_: u8 = 0;
    let mut v_depth_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4704_ = lean_st_ref_take(v___y_4702_);
                v_mctx_4705_ = crate::leanh::lean_ctor_get(v___x_4704_, 0);
                v_cache_4706_ = crate::leanh::lean_ctor_get(v___x_4704_, 1);
                v_zetaDeltaFVarIds_4707_ = crate::leanh::lean_ctor_get(v___x_4704_, 2);
                v_postponed_4708_ = crate::leanh::lean_ctor_get(v___x_4704_, 3);
                v_diag_4709_ = crate::leanh::lean_ctor_get(v___x_4704_, 4);
                v_isSharedCheck_4737_ = (!crate::leanh::lean_is_exclusive(v___x_4704_)) as u8;
                if v_isSharedCheck_4737_ == 0 {
                    v___x_4711_ = v___x_4704_;
                    v_isShared_4712_ = v_isSharedCheck_4737_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4709_);
                    crate::leanh::lean_inc(v_postponed_4708_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4707_);
                    crate::leanh::lean_inc(v_cache_4706_);
                    crate::leanh::lean_inc(v_mctx_4705_);
                    crate::leanh::lean_dec(v___x_4704_);
                    v___x_4711_ = crate::leanh::lean_box(0);
                    v_isShared_4712_ = v_isSharedCheck_4737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4713_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 0);
                v_levelAssignDepth_4714_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 1);
                v_lmvarCounter_4715_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 2);
                v_mvarCounter_4716_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 3);
                v_lDecls_4717_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 4);
                v_decls_4718_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 5);
                v_userNames_4719_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 6);
                v_lAssignment_4720_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 7);
                v_eAssignment_4721_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 8);
                v_dAssignment_4722_ = crate::leanh::lean_ctor_get(v_mctx_4705_, 9);
                v_isSharedCheck_4736_ = (!crate::leanh::lean_is_exclusive(v_mctx_4705_)) as u8;
                if v_isSharedCheck_4736_ == 0 {
                    v___x_4724_ = v_mctx_4705_;
                    v_isShared_4725_ = v_isSharedCheck_4736_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_4722_);
                    crate::leanh::lean_inc(v_eAssignment_4721_);
                    crate::leanh::lean_inc(v_lAssignment_4720_);
                    crate::leanh::lean_inc(v_userNames_4719_);
                    crate::leanh::lean_inc(v_decls_4718_);
                    crate::leanh::lean_inc(v_lDecls_4717_);
                    crate::leanh::lean_inc(v_mvarCounter_4716_);
                    crate::leanh::lean_inc(v_lmvarCounter_4715_);
                    crate::leanh::lean_inc(v_levelAssignDepth_4714_);
                    crate::leanh::lean_inc(v_depth_4713_);
                    crate::leanh::lean_dec(v_mctx_4705_);
                    v___x_4724_ = crate::leanh::lean_box(0);
                    v_isShared_4725_ = v_isSharedCheck_4736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4726_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_4721_, v_mvarId_4700_, v_val_4701_);
                if v_isShared_4725_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4724_, 8, v___x_4726_);
                    v___x_4728_ = v___x_4724_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_depth_4713_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4735_,
                        1,
                        v_levelAssignDepth_4714_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 2, v_lmvarCounter_4715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 3, v_mvarCounter_4716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 4, v_lDecls_4717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 5, v_decls_4718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 6, v_userNames_4719_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 7, v_lAssignment_4720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 8, v___x_4726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 9, v_dAssignment_4722_);
                    v___x_4728_ = v_reuseFailAlloc_4735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4711_, 0, v___x_4728_);
                    v___x_4730_ = v___x_4711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 1, v_cache_4706_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4734_,
                        2,
                        v_zetaDeltaFVarIds_4707_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 3, v_postponed_4708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 4, v_diag_4709_);
                    v___x_4730_ = v_reuseFailAlloc_4734_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4731_ = lean_st_ref_set(v___y_4702_, v___x_4730_);
                v___x_4732_ = crate::leanh::lean_box(0);
                v___x_4733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4733_, 0, v___x_4732_);
                return v___x_4733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(
    mut v_mvarId_4738_: *mut crate::leanh::LeanObject,
    mut v_val_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
        v_mvarId_4738_,
        v_val_4739_,
        v___y_4740_,
    );
    crate::leanh::lean_dec(v___y_4740_);
    return v_res_4742_;
}
pub unsafe fn l_Lean_MVarId_admit___lam__0(
    mut v_mvarId_4743_: *mut crate::leanh::LeanObject,
    mut v___x_4744_: *mut crate::leanh::LeanObject,
    mut v_synthetic_4745_: u8,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: u8 = 0;
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4765_: u8 = 0;
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4743_);
                v___x_4751_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4743_,
                    v___x_4744_,
                    v___y_4746_,
                    v___y_4747_,
                    v___y_4748_,
                    v___y_4749_,
                );
                if crate::leanh::lean_obj_tag(v___x_4751_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4751_, 1);
                    crate::leanh::lean_inc(v_mvarId_4743_);
                    v___x_4752_ = l_Lean_MVarId_getType(
                        v_mvarId_4743_,
                        v___y_4746_,
                        v___y_4747_,
                        v___y_4748_,
                        v___y_4749_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4752_) == 0 {
                        v_a_4753_ = crate::leanh::lean_ctor_get(v___x_4752_, 0);
                        crate::leanh::lean_inc(v_a_4753_);
                        crate::leanh::lean_dec_ref_known(v___x_4752_, 1);
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
                        if crate::leanh::lean_obj_tag(v___x_4755_) == 0 {
                            v_a_4756_ = crate::leanh::lean_ctor_get(v___x_4755_, 0);
                            crate::leanh::lean_inc(v_a_4756_);
                            crate::leanh::lean_dec_ref_known(v___x_4755_, 1);
                            v___x_4757_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
                                    v_mvarId_4743_,
                                    v_a_4756_,
                                    v___y_4747_,
                                );
                            return v___x_4757_;
                        } else {
                            crate::leanh::lean_dec(v_mvarId_4743_);
                            v_a_4758_ = crate::leanh::lean_ctor_get(v___x_4755_, 0);
                            v_isSharedCheck_4765_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4755_)) as u8;
                            if v_isSharedCheck_4765_ == 0 {
                                v___x_4760_ = v___x_4755_;
                                v_isShared_4761_ = v_isSharedCheck_4765_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4758_);
                                crate::leanh::lean_dec(v___x_4755_);
                                v___x_4760_ = crate::leanh::lean_box(0);
                                v_isShared_4761_ = v_isSharedCheck_4765_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_4743_);
                        v_a_4766_ = crate::leanh::lean_ctor_get(v___x_4752_, 0);
                        v_isSharedCheck_4773_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4752_)) as u8;
                        if v_isSharedCheck_4773_ == 0 {
                            v___x_4768_ = v___x_4752_;
                            v_isShared_4769_ = v_isSharedCheck_4773_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4766_);
                            crate::leanh::lean_dec(v___x_4752_);
                            v___x_4768_ = crate::leanh::lean_box(0);
                            v_isShared_4769_ = v_isSharedCheck_4773_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4743_);
                    return v___x_4751_;
                }
            }
            1 => {
                if v_isShared_4761_ == 0 {
                    v___x_4763_ = v___x_4760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
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
                    v_reuseFailAlloc_4772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
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
    mut v_mvarId_4774_: *mut crate::leanh::LeanObject,
    mut v___x_4775_: *mut crate::leanh::LeanObject,
    mut v_synthetic_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
    mut v___y_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthetic_boxed_4782_: u8 = 0;
    let mut v_res_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_4782_ = (crate::leanh::lean_unbox(v_synthetic_4776_) as u8);
    v_res_4783_ = l_Lean_MVarId_admit___lam__0(
        v_mvarId_4774_,
        v___x_4775_,
        v_synthetic_boxed_4782_,
        v___y_4777_,
        v___y_4778_,
        v___y_4779_,
        v___y_4780_,
    );
    crate::leanh::lean_dec(v___y_4780_);
    crate::leanh::lean_dec_ref(v___y_4779_);
    crate::leanh::lean_dec(v___y_4778_);
    crate::leanh::lean_dec_ref(v___y_4777_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_MVarId_admit(
    mut v_mvarId_4787_: *mut crate::leanh::LeanObject,
    mut v_synthetic_4788_: u8,
    mut v_a_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4794_ = l_Lean_MVarId_admit___closed__1;
    v___x_4795_ = crate::leanh::lean_box((v_synthetic_4788_) as usize);
    crate::leanh::lean_inc(v_mvarId_4787_);
    v___f_4796_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_admit___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4796_, 0, v_mvarId_4787_);
    crate::leanh::lean_closure_set(v___f_4796_, 1, v___x_4794_);
    crate::leanh::lean_closure_set(v___f_4796_, 2, v___x_4795_);
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
    mut v_mvarId_4798_: *mut crate::leanh::LeanObject,
    mut v_synthetic_4799_: *mut crate::leanh::LeanObject,
    mut v_a_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthetic_boxed_4805_: u8 = 0;
    let mut v_res_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_4805_ = (crate::leanh::lean_unbox(v_synthetic_4799_) as u8);
    v_res_4806_ = l_Lean_MVarId_admit(
        v_mvarId_4798_,
        v_synthetic_boxed_4805_,
        v_a_4800_,
        v_a_4801_,
        v_a_4802_,
        v_a_4803_,
    );
    crate::leanh::lean_dec(v_a_4803_);
    crate::leanh::lean_dec_ref(v_a_4802_);
    crate::leanh::lean_dec(v_a_4801_);
    crate::leanh::lean_dec_ref(v_a_4800_);
    return v_res_4806_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(
    mut v_mvarId_4807_: *mut crate::leanh::LeanObject,
    mut v_val_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
        v_mvarId_4807_,
        v_val_4808_,
        v___y_4810_,
    );
    return v___x_4814_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(
    mut v_mvarId_4815_: *mut crate::leanh::LeanObject,
    mut v_val_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4822_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(
        v_mvarId_4815_,
        v_val_4816_,
        v___y_4817_,
        v___y_4818_,
        v___y_4819_,
        v___y_4820_,
    );
    crate::leanh::lean_dec(v___y_4820_);
    crate::leanh::lean_dec_ref(v___y_4819_);
    crate::leanh::lean_dec(v___y_4818_);
    crate::leanh::lean_dec_ref(v___y_4817_);
    return v_res_4822_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(
    mut v_00_u03b2_4823_: *mut crate::leanh::LeanObject,
    mut v_x_4824_: *mut crate::leanh::LeanObject,
    mut v_x_4825_: *mut crate::leanh::LeanObject,
    mut v_x_4826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4827_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_4824_, v_x_4825_, v_x_4826_);
    return v___x_4827_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4828_: *mut crate::leanh::LeanObject,
    mut v_x_4829_: *mut crate::leanh::LeanObject,
    mut v_x_4830_: usize,
    mut v_x_4831_: usize,
    mut v_x_4832_: *mut crate::leanh::LeanObject,
    mut v_x_4833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_4829_, v_x_4830_, v_x_4831_, v_x_4832_, v_x_4833_);
    return v___x_4834_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4835_: *mut crate::leanh::LeanObject,
    mut v_x_4836_: *mut crate::leanh::LeanObject,
    mut v_x_4837_: *mut crate::leanh::LeanObject,
    mut v_x_4838_: *mut crate::leanh::LeanObject,
    mut v_x_4839_: *mut crate::leanh::LeanObject,
    mut v_x_4840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1340__boxed_4841_: usize = 0;
    let mut v_x_1341__boxed_4842_: usize = 0;
    let mut v_res_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1340__boxed_4841_ = crate::leanh::lean_unbox_usize(v_x_4837_);
    crate::leanh::lean_dec(v_x_4837_);
    v_x_1341__boxed_4842_ = crate::leanh::lean_unbox_usize(v_x_4838_);
    crate::leanh::lean_dec(v_x_4838_);
    v_res_4843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_4835_, v_x_4836_, v_x_1340__boxed_4841_, v_x_1341__boxed_4842_, v_x_4839_, v_x_4840_);
    return v_res_4843_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_4844_: *mut crate::leanh::LeanObject,
    mut v_n_4845_: *mut crate::leanh::LeanObject,
    mut v_k_4846_: *mut crate::leanh::LeanObject,
    mut v_v_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4848_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_4845_, v_k_4846_, v_v_4847_);
    return v___x_4848_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_4849_: *mut crate::leanh::LeanObject,
    mut v_depth_4850_: usize,
    mut v_keys_4851_: *mut crate::leanh::LeanObject,
    mut v_vals_4852_: *mut crate::leanh::LeanObject,
    mut v_heq_4853_: *mut crate::leanh::LeanObject,
    mut v_i_4854_: *mut crate::leanh::LeanObject,
    mut v_entries_4855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4856_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_4850_, v_keys_4851_, v_vals_4852_, v_i_4854_, v_entries_4855_);
    return v___x_4856_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_4857_: *mut crate::leanh::LeanObject,
    mut v_depth_4858_: *mut crate::leanh::LeanObject,
    mut v_keys_4859_: *mut crate::leanh::LeanObject,
    mut v_vals_4860_: *mut crate::leanh::LeanObject,
    mut v_heq_4861_: *mut crate::leanh::LeanObject,
    mut v_i_4862_: *mut crate::leanh::LeanObject,
    mut v_entries_4863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4864_: usize = 0;
    let mut v_res_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4864_ = crate::leanh::lean_unbox_usize(v_depth_4858_);
    crate::leanh::lean_dec(v_depth_4858_);
    v_res_4865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_4857_, v_depth_boxed_4864_, v_keys_4859_, v_vals_4860_, v_heq_4861_, v_i_4862_, v_entries_4863_);
    crate::leanh::lean_dec_ref(v_vals_4860_);
    crate::leanh::lean_dec_ref(v_keys_4859_);
    return v_res_4865_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_4866_: *mut crate::leanh::LeanObject,
    mut v_x_4867_: *mut crate::leanh::LeanObject,
    mut v_x_4868_: *mut crate::leanh::LeanObject,
    mut v_x_4869_: *mut crate::leanh::LeanObject,
    mut v_x_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4871_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_4867_, v_x_4868_, v_x_4869_, v_x_4870_);
    return v___x_4871_;
}
pub unsafe fn l_Lean_MVarId_headBetaType(
    mut v_mvarId_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
    mut v_a_4874_: *mut crate::leanh::LeanObject,
    mut v_a_4875_: *mut crate::leanh::LeanObject,
    mut v_a_4876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4885_: u8 = 0;
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4872_);
                v___x_4878_ = l_Lean_MVarId_getType(
                    v_mvarId_4872_,
                    v_a_4873_,
                    v_a_4874_,
                    v_a_4875_,
                    v_a_4876_,
                );
                if crate::leanh::lean_obj_tag(v___x_4878_) == 0 {
                    v_a_4879_ = crate::leanh::lean_ctor_get(v___x_4878_, 0);
                    crate::leanh::lean_inc(v_a_4879_);
                    crate::leanh::lean_dec_ref_known(v___x_4878_, 1);
                    v___x_4880_ = l_Lean_Expr_headBeta(v_a_4879_);
                    v___x_4881_ =
                        l_Lean_MVarId_setType___redArg(v_mvarId_4872_, v___x_4880_, v_a_4874_);
                    return v___x_4881_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_4872_);
                    v_a_4882_ = crate::leanh::lean_ctor_get(v___x_4878_, 0);
                    v_isSharedCheck_4889_ = (!crate::leanh::lean_is_exclusive(v___x_4878_)) as u8;
                    if v_isSharedCheck_4889_ == 0 {
                        v___x_4884_ = v___x_4878_;
                        v_isShared_4885_ = v_isSharedCheck_4889_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4882_);
                        crate::leanh::lean_dec(v___x_4878_);
                        v___x_4884_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4888_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
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
    mut v_mvarId_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
    mut v_a_4893_: *mut crate::leanh::LeanObject,
    mut v_a_4894_: *mut crate::leanh::LeanObject,
    mut v_a_4895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4896_ =
        l_Lean_MVarId_headBetaType(v_mvarId_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
    crate::leanh::lean_dec(v_a_4894_);
    crate::leanh::lean_dec_ref(v_a_4893_);
    crate::leanh::lean_dec(v_a_4892_);
    crate::leanh::lean_dec_ref(v_a_4891_);
    return v_res_4896_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(
    mut v_a_4897_: *mut crate::leanh::LeanObject,
    mut v_x_4898_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4899_: u8 = 0;
    let mut v_key_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4898_) == 0 {
                    v___x_4899_ = 0;
                    return v___x_4899_;
                } else {
                    v_key_4900_ = crate::leanh::lean_ctor_get(v_x_4898_, 0);
                    v_tail_4901_ = crate::leanh::lean_ctor_get(v_x_4898_, 2);
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
    mut v_a_4904_: *mut crate::leanh::LeanObject,
    mut v_x_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4906_: u8 = 0;
    let mut v_r_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4906_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_4904_, v_x_4905_);
    crate::leanh::lean_dec(v_x_4905_);
    crate::leanh::lean_dec(v_a_4904_);
    v_r_4907_ = crate::leanh::lean_box((v_res_4906_) as usize);
    return v_r_4907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(
    mut v_a_4908_: *mut crate::leanh::LeanObject,
    mut v_x_4909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v___x_4916_: u8 = 0;
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4909_) == 0 {
                    return v_x_4909_;
                } else {
                    v_key_4910_ = crate::leanh::lean_ctor_get(v_x_4909_, 0);
                    v_value_4911_ = crate::leanh::lean_ctor_get(v_x_4909_, 1);
                    v_tail_4912_ = crate::leanh::lean_ctor_get(v_x_4909_, 2);
                    v_isSharedCheck_4921_ = (!crate::leanh::lean_is_exclusive(v_x_4909_)) as u8;
                    if v_isSharedCheck_4921_ == 0 {
                        v___x_4914_ = v_x_4909_;
                        v_isShared_4915_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4912_);
                        crate::leanh::lean_inc(v_value_4911_);
                        crate::leanh::lean_inc(v_key_4910_);
                        crate::leanh::lean_dec(v_x_4909_);
                        v___x_4914_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_4914_, 2, v___x_4917_);
                        v___x_4919_ = v___x_4914_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4920_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_key_4910_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_value_4911_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4920_, 2, v___x_4917_);
                        v___x_4919_ = v_reuseFailAlloc_4920_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4914_);
                    crate::leanh::lean_dec(v_value_4911_);
                    crate::leanh::lean_dec(v_key_4910_);
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
    mut v_a_4922_: *mut crate::leanh::LeanObject,
    mut v_x_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_4922_, v_x_4923_);
    crate::leanh::lean_dec(v_a_4922_);
    return v_res_4924_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(
    mut v_m_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4956_: u8 = 0;
    let mut v_unused_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4927_ = crate::leanh::lean_ctor_get(v_m_4925_, 0);
                v_buckets_4928_ = crate::leanh::lean_ctor_get(v_m_4925_, 1);
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
                    crate::leanh::lean_inc(v_bkt_4942_);
                    crate::leanh::lean_inc_ref(v_buckets_4928_);
                    crate::leanh::lean_inc(v_size_4927_);
                    v_isSharedCheck_4956_ = (!crate::leanh::lean_is_exclusive(v_m_4925_)) as u8;
                    if v_isSharedCheck_4956_ == 0 {
                        v_unused_4957_ = crate::leanh::lean_ctor_get(v_m_4925_, 1);
                        crate::leanh::lean_dec(v_unused_4957_);
                        v_unused_4958_ = crate::leanh::lean_ctor_get(v_m_4925_, 0);
                        crate::leanh::lean_dec(v_unused_4958_);
                        v___x_4945_ = v_m_4925_;
                        v_isShared_4946_ = v_isSharedCheck_4956_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4925_);
                        v___x_4945_ = crate::leanh::lean_box(0);
                        v_isShared_4946_ = v_isSharedCheck_4956_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4947_ = crate::leanh::lean_box(0);
                v_buckets_x27_4948_ = lean_array_uset(v_buckets_4928_, v___x_4941_, v___x_4947_);
                v___x_4949_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4950_ = lean_nat_sub(v_size_4927_, v___x_4949_);
                crate::leanh::lean_dec(v_size_4927_);
                v___x_4951_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_4926_, v_bkt_4942_);
                v___x_4952_ = lean_array_uset(v_buckets_x27_4948_, v___x_4941_, v___x_4951_);
                if v_isShared_4946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4945_, 1, v___x_4952_);
                    crate::leanh::lean_ctor_set(v___x_4945_, 0, v___x_4950_);
                    v___x_4954_ = v___x_4945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 1, v___x_4952_);
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
    mut v_m_4959_: *mut crate::leanh::LeanObject,
    mut v_a_4960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4961_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_4959_, v_a_4960_);
    crate::leanh::lean_dec(v_a_4960_);
    return v_res_4961_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__0(
    mut v_e_4962_: *mut crate::leanh::LeanObject,
    mut v___y_4963_: *mut crate::leanh::LeanObject,
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
    mut v___y_4967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4969_ = lean_st_ref_take(v___y_4963_);
    v___x_4970_ = l_Lean_Expr_fvarId_x21(v_e_4962_);
    v___x_4971_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_4969_, v___x_4970_);
    crate::leanh::lean_dec(v___x_4970_);
    v___x_4972_ = lean_st_ref_set(v___y_4963_, v___x_4971_);
    v___x_4973_ = crate::leanh::lean_box(0);
    v___x_4974_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4974_, 0, v___x_4973_);
    return v___x_4974_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(
    mut v_e_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
    mut v___y_4978_: *mut crate::leanh::LeanObject,
    mut v___y_4979_: *mut crate::leanh::LeanObject,
    mut v___y_4980_: *mut crate::leanh::LeanObject,
    mut v___y_4981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Lean_MVarId_getNondepPropHyps___lam__0(
        v_e_4975_,
        v___y_4976_,
        v___y_4977_,
        v___y_4978_,
        v___y_4979_,
        v___y_4980_,
    );
    crate::leanh::lean_dec(v___y_4980_);
    crate::leanh::lean_dec_ref(v___y_4979_);
    crate::leanh::lean_dec(v___y_4978_);
    crate::leanh::lean_dec_ref(v___y_4977_);
    crate::leanh::lean_dec(v___y_4976_);
    crate::leanh::lean_dec_ref(v_e_4975_);
    return v_res_4982_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__1(
    mut v_____r_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
    mut v___y_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
    mut v___y_4988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4990_ = lean_st_ref_get(v___y_4984_);
    v___x_4991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4991_, 0, v___x_4990_);
    return v___x_4991_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(
    mut v_____r_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4999_ = l_Lean_MVarId_getNondepPropHyps___lam__1(
        v_____r_4992_,
        v___y_4993_,
        v___y_4994_,
        v___y_4995_,
        v___y_4996_,
        v___y_4997_,
    );
    crate::leanh::lean_dec(v___y_4997_);
    crate::leanh::lean_dec_ref(v___y_4996_);
    crate::leanh::lean_dec(v___y_4995_);
    crate::leanh::lean_dec_ref(v___y_4994_);
    crate::leanh::lean_dec(v___y_4993_);
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
    mut v_e_5003_: *mut crate::leanh::LeanObject,
    mut v_a_5004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: usize = 0;
    let mut v___x_5009_: usize = 0;
    let mut v___x_5010_: usize = 0;
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: usize = 0;
    let mut v___x_5013_: u8 = 0;
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5027_: u8 = 0;
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5006_ = lean_st_ref_get(v_a_5004_);
                v_visited_5007_ = crate::leanh::lean_ctor_get(v___x_5006_, 0);
                crate::leanh::lean_inc_ref(v_visited_5007_);
                crate::leanh::lean_dec(v___x_5006_);
                v___x_5008_ = lean_ptr_addr(v_e_5003_);
                v___x_5009_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0);
                v___x_5010_ = lean_usize_mod(v___x_5008_, v___x_5009_);
                v___x_5011_ = lean_array_uget(v_visited_5007_, v___x_5010_);
                crate::leanh::lean_dec_ref(v_visited_5007_);
                v___x_5012_ = lean_ptr_addr(v___x_5011_);
                crate::leanh::lean_dec(v___x_5011_);
                v___x_5013_ = lean_usize_dec_eq(v___x_5012_, v___x_5008_);
                if v___x_5013_ == 0 {
                    v___x_5014_ = lean_st_ref_take(v_a_5004_);
                    v_visited_5015_ = crate::leanh::lean_ctor_get(v___x_5014_, 0);
                    v_checked_5016_ = crate::leanh::lean_ctor_get(v___x_5014_, 1);
                    v_isSharedCheck_5027_ = (!crate::leanh::lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5027_ == 0 {
                        v___x_5018_ = v___x_5014_;
                        v_isShared_5019_ = v_isSharedCheck_5027_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_checked_5016_);
                        crate::leanh::lean_inc(v_visited_5015_);
                        crate::leanh::lean_dec(v___x_5014_);
                        v___x_5018_ = crate::leanh::lean_box(0);
                        v_isShared_5019_ = v_isSharedCheck_5027_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5003_);
                    v___x_5028_ = crate::leanh::lean_box((v___x_5013_) as usize);
                    v___x_5029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5029_, 0, v___x_5028_);
                    return v___x_5029_;
                }
            }
            1 => {
                v___x_5020_ = lean_array_uset(v_visited_5015_, v___x_5010_, v_e_5003_);
                if v_isShared_5019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5018_, 0, v___x_5020_);
                    v___x_5022_ = v___x_5018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5026_, 1, v_checked_5016_);
                    v___x_5022_ = v_reuseFailAlloc_5026_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5023_ = lean_st_ref_set(v_a_5004_, v___x_5022_);
                v___x_5024_ = crate::leanh::lean_box((v___x_5013_) as usize);
                v___x_5025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5025_, 0, v___x_5024_);
                return v___x_5025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(
    mut v_e_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5033_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_5030_, v_a_5031_);
    crate::leanh::lean_dec(v_a_5031_);
    return v_res_5033_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(
    mut v_a_5034_: *mut crate::leanh::LeanObject,
    mut v_x_5035_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5036_: u8 = 0;
    let mut v_key_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5035_) == 0 {
                    v___x_5036_ = 0;
                    return v___x_5036_;
                } else {
                    v_key_5037_ = crate::leanh::lean_ctor_get(v_x_5035_, 0);
                    v_tail_5038_ = crate::leanh::lean_ctor_get(v_x_5035_, 2);
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
    mut v_a_5041_: *mut crate::leanh::LeanObject,
    mut v_x_5042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5043_: u8 = 0;
    let mut v_r_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5043_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_5041_, v_x_5042_);
    crate::leanh::lean_dec(v_x_5042_);
    crate::leanh::lean_dec_ref(v_a_5041_);
    v_r_5044_ = crate::leanh::lean_box((v_res_5043_) as usize);
    return v_r_5044_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(
    mut v_x_5045_: *mut crate::leanh::LeanObject,
    mut v_x_5046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5046_) == 0 {
                    return v_x_5045_;
                } else {
                    v_key_5047_ = crate::leanh::lean_ctor_get(v_x_5046_, 0);
                    v_value_5048_ = crate::leanh::lean_ctor_get(v_x_5046_, 1);
                    v_tail_5049_ = crate::leanh::lean_ctor_get(v_x_5046_, 2);
                    v_isSharedCheck_5072_ = (!crate::leanh::lean_is_exclusive(v_x_5046_)) as u8;
                    if v_isSharedCheck_5072_ == 0 {
                        v___x_5051_ = v_x_5046_;
                        v_isShared_5052_ = v_isSharedCheck_5072_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5049_);
                        crate::leanh::lean_inc(v_value_5048_);
                        crate::leanh::lean_inc(v_key_5047_);
                        crate::leanh::lean_dec(v_x_5046_);
                        v___x_5051_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_5066_);
                if v_isShared_5052_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5051_, 2, v___x_5066_);
                    v___x_5068_ = v___x_5051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5071_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_key_5047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5071_, 1, v_value_5048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5071_, 2, v___x_5066_);
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
    mut v_i_5073_: *mut crate::leanh::LeanObject,
    mut v_source_5074_: *mut crate::leanh::LeanObject,
    mut v_target_5075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut v_es_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5076_ = lean_array_get_size(v_source_5074_);
                v___x_5077_ = lean_nat_dec_lt(v_i_5073_, v___x_5076_);
                if v___x_5077_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5074_);
                    crate::leanh::lean_dec(v_i_5073_);
                    return v_target_5075_;
                } else {
                    v_es_5078_ = lean_array_fget(v_source_5074_, v_i_5073_);
                    v___x_5079_ = crate::leanh::lean_box(0);
                    v_source_5080_ = lean_array_fset(v_source_5074_, v_i_5073_, v___x_5079_);
                    v_target_5081_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_5075_, v_es_5078_);
                    v___x_5082_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5083_ = lean_nat_add(v_i_5073_, v___x_5082_);
                    crate::leanh::lean_dec(v_i_5073_);
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
    mut v_data_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = lean_array_get_size(v_data_5085_);
    v___x_5087_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5088_ = lean_nat_mul(v___x_5086_, v___x_5087_);
    v___x_5089_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5090_ = crate::leanh::lean_box(0);
    v___x_5091_ = lean_mk_array(v_nbuckets_5088_, v___x_5090_);
    v___x_5092_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_5089_, v_data_5085_, v___x_5091_);
    return v___x_5092_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(
    mut v_m_5093_: *mut crate::leanh::LeanObject,
    mut v_a_5094_: *mut crate::leanh::LeanObject,
    mut v_b_5095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: u8 = 0;
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: u8 = 0;
    let mut v_val_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut v_unused_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5096_ = crate::leanh::lean_ctor_get(v_m_5093_, 0);
                v_buckets_5097_ = crate::leanh::lean_ctor_get(v_m_5093_, 1);
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
                    crate::leanh::lean_inc_ref(v_buckets_5097_);
                    crate::leanh::lean_inc(v_size_5096_);
                    v_isSharedCheck_5133_ = (!crate::leanh::lean_is_exclusive(v_m_5093_)) as u8;
                    if v_isSharedCheck_5133_ == 0 {
                        v_unused_5134_ = crate::leanh::lean_ctor_get(v_m_5093_, 1);
                        crate::leanh::lean_dec(v_unused_5134_);
                        v_unused_5135_ = crate::leanh::lean_ctor_get(v_m_5093_, 0);
                        crate::leanh::lean_dec(v_unused_5135_);
                        v___x_5114_ = v_m_5093_;
                        v_isShared_5115_ = v_isSharedCheck_5133_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_5093_);
                        v___x_5114_ = crate::leanh::lean_box(0);
                        v_isShared_5115_ = v_isSharedCheck_5133_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_5095_);
                    crate::leanh::lean_dec_ref(v_a_5094_);
                    return v_m_5093_;
                }
            }
            1 => {
                v___x_5116_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_5117_ = lean_nat_add(v_size_5096_, v___x_5116_);
                crate::leanh::lean_dec(v_size_5096_);
                crate::leanh::lean_inc(v_bkt_5111_);
                v___x_5118_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5118_, 0, v_a_5094_);
                crate::leanh::lean_ctor_set(v___x_5118_, 1, v_b_5095_);
                crate::leanh::lean_ctor_set(v___x_5118_, 2, v_bkt_5111_);
                v_buckets_x27_5119_ = lean_array_uset(v_buckets_5097_, v___x_5110_, v___x_5118_);
                v___x_5120_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_5121_ = lean_nat_mul(v_size_x27_5117_, v___x_5120_);
                v___x_5122_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5123_ = lean_nat_div(v___x_5121_, v___x_5122_);
                crate::leanh::lean_dec(v___x_5121_);
                v___x_5124_ = lean_array_get_size(v_buckets_x27_5119_);
                v___x_5125_ = lean_nat_dec_le(v___x_5123_, v___x_5124_);
                crate::leanh::lean_dec(v___x_5123_);
                if v___x_5125_ == 0 {
                    v_val_5126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_5119_);
                    if v_isShared_5115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5114_, 1, v_val_5126_);
                        crate::leanh::lean_ctor_set(v___x_5114_, 0, v_size_x27_5117_);
                        v___x_5128_ = v___x_5114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_size_x27_5117_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5129_, 1, v_val_5126_);
                        v___x_5128_ = v_reuseFailAlloc_5129_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5114_, 1, v_buckets_x27_5119_);
                        crate::leanh::lean_ctor_set(v___x_5114_, 0, v_size_x27_5117_);
                        v___x_5131_ = v___x_5114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_size_x27_5117_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 1, v_buckets_x27_5119_);
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
    mut v_m_5136_: *mut crate::leanh::LeanObject,
    mut v_a_5137_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: u8 = 0;
    v_buckets_5138_ = crate::leanh::lean_ctor_get(v_m_5136_, 1);
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
    mut v_m_5154_: *mut crate::leanh::LeanObject,
    mut v_a_5155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5156_: u8 = 0;
    let mut v_r_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_5154_, v_a_5155_);
    crate::leanh::lean_dec_ref(v_a_5155_);
    crate::leanh::lean_dec_ref(v_m_5154_);
    v_r_5157_ = crate::leanh::lean_box((v_res_5156_) as usize);
    return v_r_5157_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(
    mut v_e_5158_: *mut crate::leanh::LeanObject,
    mut v_a_5159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: u8 = 0;
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5161_ = lean_st_ref_get(v_a_5159_);
                v_checked_5162_ = crate::leanh::lean_ctor_get(v___x_5161_, 1);
                crate::leanh::lean_inc_ref(v_checked_5162_);
                crate::leanh::lean_dec(v___x_5161_);
                v___x_5163_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_5162_, v_e_5158_);
                crate::leanh::lean_dec_ref(v_checked_5162_);
                if v___x_5163_ == 0 {
                    v___x_5164_ = lean_st_ref_take(v_a_5159_);
                    v_visited_5165_ = crate::leanh::lean_ctor_get(v___x_5164_, 0);
                    v_checked_5166_ = crate::leanh::lean_ctor_get(v___x_5164_, 1);
                    v_isSharedCheck_5178_ = (!crate::leanh::lean_is_exclusive(v___x_5164_)) as u8;
                    if v_isSharedCheck_5178_ == 0 {
                        v___x_5168_ = v___x_5164_;
                        v_isShared_5169_ = v_isSharedCheck_5178_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_checked_5166_);
                        crate::leanh::lean_inc(v_visited_5165_);
                        crate::leanh::lean_dec(v___x_5164_);
                        v___x_5168_ = crate::leanh::lean_box(0);
                        v_isShared_5169_ = v_isSharedCheck_5178_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5158_);
                    v___x_5179_ = crate::leanh::lean_box((v___x_5163_) as usize);
                    v___x_5180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5180_, 0, v___x_5179_);
                    return v___x_5180_;
                }
            }
            1 => {
                v___x_5170_ = crate::leanh::lean_box(0);
                v___x_5171_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_5166_, v_e_5158_, v___x_5170_);
                if v_isShared_5169_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5168_, 1, v___x_5171_);
                    v___x_5173_ = v___x_5168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_visited_5165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5177_, 1, v___x_5171_);
                    v___x_5173_ = v_reuseFailAlloc_5177_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5174_ = lean_st_ref_set(v_a_5159_, v___x_5173_);
                v___x_5175_ = crate::leanh::lean_box((v___x_5163_) as usize);
                v___x_5176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5176_, 0, v___x_5175_);
                return v___x_5176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_e_5181_: *mut crate::leanh::LeanObject,
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5184_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_5181_, v_a_5182_);
    crate::leanh::lean_dec(v_a_5182_);
    return v_res_5184_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(
    mut v_p_5185_: *mut crate::leanh::LeanObject,
    mut v_f_5186_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_5187_: u8,
    mut v_e_5188_: *mut crate::leanh::LeanObject,
    mut v_a_5189_: *mut crate::leanh::LeanObject,
    mut v___y_5190_: *mut crate::leanh::LeanObject,
    mut v___y_5191_: *mut crate::leanh::LeanObject,
    mut v___y_5192_: *mut crate::leanh::LeanObject,
    mut v___y_5193_: *mut crate::leanh::LeanObject,
    mut v___y_5194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: u8 = 0;
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u8 = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5248_: u8 = 0;
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v_unused_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_a_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_5188_);
                v___x_5234_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_5188_, v_a_5189_);
                if crate::leanh::lean_obj_tag(v___x_5234_) == 0 {
                    v_a_5235_ = crate::leanh::lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5267_ = (!crate::leanh::lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5267_ == 0 {
                        v___x_5237_ = v___x_5234_;
                        v_isShared_5238_ = v_isSharedCheck_5267_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5235_);
                        crate::leanh::lean_dec(v___x_5234_);
                        v___x_5237_ = crate::leanh::lean_box(0);
                        v_isShared_5238_ = v_isSharedCheck_5267_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5188_);
                    crate::leanh::lean_dec_ref(v_f_5186_);
                    crate::leanh::lean_dec_ref(v_p_5185_);
                    v_a_5268_ = crate::leanh::lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5275_ = (!crate::leanh::lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5275_ == 0 {
                        v___x_5270_ = v___x_5234_;
                        v_isShared_5271_ = v_isSharedCheck_5275_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5268_);
                        crate::leanh::lean_dec(v___x_5234_);
                        v___x_5270_ = crate::leanh::lean_box(0);
                        v_isShared_5271_ = v_isSharedCheck_5275_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_5186_);
                crate::leanh::lean_inc_ref(v_p_5185_);
                v___x_5205_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_d_5202_, v___y_5204_, v___y_5200_, v___y_5198_, v___y_5199_, v___y_5197_, v___y_5201_);
                if crate::leanh::lean_obj_tag(v___x_5205_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5205_, 1);
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
                    crate::leanh::lean_dec_ref(v_b_5203_);
                    crate::leanh::lean_dec_ref(v_f_5186_);
                    crate::leanh::lean_dec_ref(v_p_5185_);
                    return v___x_5205_;
                }
            }
            2 => match crate::leanh::lean_obj_tag(v_e_5188_) {
                7 => {
                    v_binderType_5214_ = crate::leanh::lean_ctor_get(v_e_5188_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_5214_);
                    v_body_5215_ = crate::leanh::lean_ctor_get(v_e_5188_, 2);
                    crate::leanh::lean_inc_ref(v_body_5215_);
                    crate::leanh::lean_dec_ref_known(v_e_5188_, 3);
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
                    v_binderType_5216_ = crate::leanh::lean_ctor_get(v_e_5188_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_5216_);
                    v_body_5217_ = crate::leanh::lean_ctor_get(v_e_5188_, 2);
                    crate::leanh::lean_inc_ref(v_body_5217_);
                    crate::leanh::lean_dec_ref_known(v_e_5188_, 3);
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
                    v_type_5218_ = crate::leanh::lean_ctor_get(v_e_5188_, 1);
                    crate::leanh::lean_inc_ref(v_type_5218_);
                    v_value_5219_ = crate::leanh::lean_ctor_get(v_e_5188_, 2);
                    crate::leanh::lean_inc_ref(v_value_5219_);
                    v_body_5220_ = crate::leanh::lean_ctor_get(v_e_5188_, 3);
                    crate::leanh::lean_inc_ref(v_body_5220_);
                    crate::leanh::lean_dec_ref_known(v_e_5188_, 4);
                    crate::leanh::lean_inc_ref(v_f_5186_);
                    crate::leanh::lean_inc_ref(v_p_5185_);
                    v___x_5221_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_type_5218_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
                    if crate::leanh::lean_obj_tag(v___x_5221_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5221_, 1);
                        crate::leanh::lean_inc_ref(v_f_5186_);
                        crate::leanh::lean_inc_ref(v_p_5185_);
                        v___x_5222_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_value_5219_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
                        if crate::leanh::lean_obj_tag(v___x_5222_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5222_, 1);
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
                            crate::leanh::lean_dec_ref(v_body_5220_);
                            crate::leanh::lean_dec_ref(v_f_5186_);
                            crate::leanh::lean_dec_ref(v_p_5185_);
                            return v___x_5222_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_5220_);
                        crate::leanh::lean_dec_ref(v_value_5219_);
                        crate::leanh::lean_dec_ref(v_f_5186_);
                        crate::leanh::lean_dec_ref(v_p_5185_);
                        return v___x_5221_;
                    }
                }
                5 => {
                    v_fn_5224_ = crate::leanh::lean_ctor_get(v_e_5188_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5224_);
                    v_arg_5225_ = crate::leanh::lean_ctor_get(v_e_5188_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5225_);
                    crate::leanh::lean_dec_ref_known(v_e_5188_, 2);
                    crate::leanh::lean_inc_ref(v_f_5186_);
                    crate::leanh::lean_inc_ref(v_p_5185_);
                    v___x_5226_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_fn_5224_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
                    if crate::leanh::lean_obj_tag(v___x_5226_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5226_, 1);
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
                        crate::leanh::lean_dec_ref(v_arg_5225_);
                        crate::leanh::lean_dec_ref(v_f_5186_);
                        crate::leanh::lean_dec_ref(v_p_5185_);
                        return v___x_5226_;
                    }
                }
                10 => {
                    v_expr_5228_ = crate::leanh::lean_ctor_get(v_e_5188_, 1);
                    crate::leanh::lean_inc_ref(v_expr_5228_);
                    crate::leanh::lean_dec_ref_known(v_e_5188_, 2);
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
                    v_struct_5230_ = crate::leanh::lean_ctor_get(v_e_5188_, 2);
                    crate::leanh::lean_inc_ref(v_struct_5230_);
                    crate::leanh::lean_dec_ref_known(v_e_5188_, 3);
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
                    crate::leanh::lean_dec_ref(v_e_5188_);
                    crate::leanh::lean_dec_ref(v_f_5186_);
                    crate::leanh::lean_dec_ref(v_p_5185_);
                    v___x_5232_ = crate::leanh::lean_box(0);
                    v___x_5233_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5233_, 0, v___x_5232_);
                    return v___x_5233_;
                }
            },
            3 => {
                v___x_5239_ = (crate::leanh::lean_unbox(v_a_5235_) as u8);
                crate::leanh::lean_dec(v_a_5235_);
                if v___x_5239_ == 0 {
                    crate::leanh::lean_del_object(v___x_5237_);
                    crate::leanh::lean_inc_ref(v_p_5185_);
                    crate::leanh::lean_inc_ref(v_e_5188_);
                    v___x_5240_ = crate::leanh::lean_apply_1(v_p_5185_, v_e_5188_);
                    v___x_5241_ = (crate::leanh::lean_unbox(v___x_5240_) as u8);
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
                        crate::leanh::lean_inc_ref(v_e_5188_);
                        v___x_5242_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_5188_, v_a_5189_);
                        if crate::leanh::lean_obj_tag(v___x_5242_) == 0 {
                            v_a_5243_ = crate::leanh::lean_ctor_get(v___x_5242_, 0);
                            crate::leanh::lean_inc(v_a_5243_);
                            crate::leanh::lean_dec_ref_known(v___x_5242_, 1);
                            v___x_5244_ = (crate::leanh::lean_unbox(v_a_5243_) as u8);
                            crate::leanh::lean_dec(v_a_5243_);
                            if v___x_5244_ == 0 {
                                crate::leanh::lean_inc_ref(v_f_5186_);
                                crate::leanh::lean_inc(v___y_5194_);
                                crate::leanh::lean_inc_ref(v___y_5193_);
                                crate::leanh::lean_inc(v___y_5192_);
                                crate::leanh::lean_inc_ref(v___y_5191_);
                                crate::leanh::lean_inc(v___y_5190_);
                                crate::leanh::lean_inc_ref(v_e_5188_);
                                v___x_5245_ = crate::leanh::lean_apply_7(
                                    v_f_5186_,
                                    v_e_5188_,
                                    v___y_5190_,
                                    v___y_5191_,
                                    v___y_5192_,
                                    v___y_5193_,
                                    v___y_5194_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_5245_) == 0 {
                                    v_isSharedCheck_5253_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5245_)) as u8;
                                    if v_isSharedCheck_5253_ == 0 {
                                        v_unused_5254_ =
                                            crate::leanh::lean_ctor_get(v___x_5245_, 0);
                                        crate::leanh::lean_dec(v_unused_5254_);
                                        v___x_5247_ = v___x_5245_;
                                        v_isShared_5248_ = v_isSharedCheck_5253_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_5245_);
                                        v___x_5247_ = crate::leanh::lean_box(0);
                                        v_isShared_5248_ = v_isSharedCheck_5253_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_e_5188_);
                                    crate::leanh::lean_dec_ref(v_f_5186_);
                                    crate::leanh::lean_dec_ref(v_p_5185_);
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
                            crate::leanh::lean_dec_ref(v_e_5188_);
                            crate::leanh::lean_dec_ref(v_f_5186_);
                            crate::leanh::lean_dec_ref(v_p_5185_);
                            v_a_5255_ = crate::leanh::lean_ctor_get(v___x_5242_, 0);
                            v_isSharedCheck_5262_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5242_)) as u8;
                            if v_isSharedCheck_5262_ == 0 {
                                v___x_5257_ = v___x_5242_;
                                v_isShared_5258_ = v_isSharedCheck_5262_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5255_);
                                crate::leanh::lean_dec(v___x_5242_);
                                v___x_5257_ = crate::leanh::lean_box(0);
                                v_isShared_5258_ = v_isSharedCheck_5262_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5188_);
                    crate::leanh::lean_dec_ref(v_f_5186_);
                    crate::leanh::lean_dec_ref(v_p_5185_);
                    v___x_5263_ = crate::leanh::lean_box(0);
                    if v_isShared_5238_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5263_);
                        v___x_5265_ = v___x_5237_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5266_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5263_);
                        v___x_5265_ = v_reuseFailAlloc_5266_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_stopWhenVisited_5187_ == 0 {
                    crate::leanh::lean_del_object(v___x_5247_);
                    v___y_5208_ = v_a_5189_;
                    v___y_5209_ = v___y_5190_;
                    v___y_5210_ = v___y_5191_;
                    v___y_5211_ = v___y_5192_;
                    v___y_5212_ = v___y_5193_;
                    v___y_5213_ = v___y_5194_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_5188_);
                    crate::leanh::lean_dec_ref(v_f_5186_);
                    crate::leanh::lean_dec_ref(v_p_5185_);
                    v___x_5249_ = crate::leanh::lean_box(0);
                    if v_isShared_5248_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5247_, 0, v___x_5249_);
                        v___x_5251_ = v___x_5247_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
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
                    v_reuseFailAlloc_5261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
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
                    v_reuseFailAlloc_5274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
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
    mut v_p_5276_: *mut crate::leanh::LeanObject,
    mut v_f_5277_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_5278_: *mut crate::leanh::LeanObject,
    mut v_e_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
    mut v___y_5284_: *mut crate::leanh::LeanObject,
    mut v___y_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_5287_: u8 = 0;
    let mut v_res_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_5287_ = (crate::leanh::lean_unbox(v_stopWhenVisited_5278_) as u8);
    v_res_5288_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5276_, v_f_5277_, v_stopWhenVisited_boxed_5287_, v_e_5279_, v_a_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
    crate::leanh::lean_dec(v___y_5285_);
    crate::leanh::lean_dec_ref(v___y_5284_);
    crate::leanh::lean_dec(v___y_5283_);
    crate::leanh::lean_dec_ref(v___y_5282_);
    crate::leanh::lean_dec(v___y_5281_);
    crate::leanh::lean_dec(v_a_5280_);
    return v_res_5288_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(
    mut v_p_5289_: *mut crate::leanh::LeanObject,
    mut v_f_5290_: *mut crate::leanh::LeanObject,
    mut v_e_5291_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_5292_: u8,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5305_: u8 = 0;
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5299_ = l_Lean_ForEachExprWhere_initCache;
                v___x_5300_ = lean_st_mk_ref(v___x_5299_);
                v___x_5301_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5289_, v_f_5290_, v_stopWhenVisited_5292_, v_e_5291_, v___x_5300_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
                if crate::leanh::lean_obj_tag(v___x_5301_) == 0 {
                    v_a_5302_ = crate::leanh::lean_ctor_get(v___x_5301_, 0);
                    v_isSharedCheck_5310_ = (!crate::leanh::lean_is_exclusive(v___x_5301_)) as u8;
                    if v_isSharedCheck_5310_ == 0 {
                        v___x_5304_ = v___x_5301_;
                        v_isShared_5305_ = v_isSharedCheck_5310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5302_);
                        crate::leanh::lean_dec(v___x_5301_);
                        v___x_5304_ = crate::leanh::lean_box(0);
                        v_isShared_5305_ = v_isSharedCheck_5310_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5300_);
                    return v___x_5301_;
                }
            }
            1 => {
                v___x_5306_ = lean_st_ref_get(v___x_5300_);
                crate::leanh::lean_dec(v___x_5300_);
                crate::leanh::lean_dec(v___x_5306_);
                if v_isShared_5305_ == 0 {
                    v___x_5308_ = v___x_5304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5302_);
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
    mut v_p_5311_: *mut crate::leanh::LeanObject,
    mut v_f_5312_: *mut crate::leanh::LeanObject,
    mut v_e_5313_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
    mut v___y_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
    mut v___y_5319_: *mut crate::leanh::LeanObject,
    mut v___y_5320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_5321_: u8 = 0;
    let mut v_res_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_5321_ = (crate::leanh::lean_unbox(v_stopWhenVisited_5314_) as u8);
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
    crate::leanh::lean_dec(v___y_5319_);
    crate::leanh::lean_dec_ref(v___y_5318_);
    crate::leanh::lean_dec(v___y_5317_);
    crate::leanh::lean_dec_ref(v___y_5316_);
    crate::leanh::lean_dec(v___y_5315_);
    return v_res_5322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(
    mut v___f_5324_: *mut crate::leanh::LeanObject,
    mut v___f_5325_: *mut crate::leanh::LeanObject,
    mut v___x_5326_: u8,
    mut v_e_5327_: *mut crate::leanh::LeanObject,
    mut v_candidates_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
    mut v___y_5330_: *mut crate::leanh::LeanObject,
    mut v___y_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v___x_5348_: u8 = 0;
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut v_a_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5366_: u8 = 0;
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_5334_) == 0 {
                    v_a_5335_ = crate::leanh::lean_ctor_get(v___x_5334_, 0);
                    crate::leanh::lean_inc(v_a_5335_);
                    crate::leanh::lean_dec_ref_known(v___x_5334_, 1);
                    v___x_5336_ = lean_st_mk_ref(v_candidates_5328_);
                    v___x_5348_ = l_Lean_Expr_hasFVar(v_a_5335_);
                    if v___x_5348_ == 0 {
                        crate::leanh::lean_dec(v_a_5335_);
                        crate::leanh::lean_dec_ref(v___f_5325_);
                        v___x_5349_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v___y_5332_);
                        crate::leanh::lean_inc_ref(v___y_5331_);
                        crate::leanh::lean_inc(v___y_5330_);
                        crate::leanh::lean_inc_ref(v___y_5329_);
                        crate::leanh::lean_inc(v___x_5336_);
                        v___x_5350_ = crate::leanh::lean_apply_7(
                            v___f_5324_,
                            v___x_5349_,
                            v___x_5336_,
                            v___y_5329_,
                            v___y_5330_,
                            v___y_5331_,
                            v___y_5332_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_5338_ = v___x_5350_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0;
                        v___x_5352_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_5351_, v___f_5325_, v_a_5335_, v___x_5326_, v___x_5336_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
                        if crate::leanh::lean_obj_tag(v___x_5352_) == 0 {
                            v_a_5353_ = crate::leanh::lean_ctor_get(v___x_5352_, 0);
                            crate::leanh::lean_inc(v_a_5353_);
                            crate::leanh::lean_dec_ref_known(v___x_5352_, 1);
                            crate::leanh::lean_inc(v___y_5332_);
                            crate::leanh::lean_inc_ref(v___y_5331_);
                            crate::leanh::lean_inc(v___y_5330_);
                            crate::leanh::lean_inc_ref(v___y_5329_);
                            crate::leanh::lean_inc(v___x_5336_);
                            v___x_5354_ = crate::leanh::lean_apply_7(
                                v___f_5324_,
                                v_a_5353_,
                                v___x_5336_,
                                v___y_5329_,
                                v___y_5330_,
                                v___y_5331_,
                                v___y_5332_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_5338_ = v___x_5354_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5336_);
                            crate::leanh::lean_dec_ref(v___f_5324_);
                            v_a_5355_ = crate::leanh::lean_ctor_get(v___x_5352_, 0);
                            v_isSharedCheck_5362_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5352_)) as u8;
                            if v_isSharedCheck_5362_ == 0 {
                                v___x_5357_ = v___x_5352_;
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5355_);
                                crate::leanh::lean_dec(v___x_5352_);
                                v___x_5357_ = crate::leanh::lean_box(0);
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_candidates_5328_);
                    crate::leanh::lean_dec_ref(v___f_5325_);
                    crate::leanh::lean_dec_ref(v___f_5324_);
                    v_a_5363_ = crate::leanh::lean_ctor_get(v___x_5334_, 0);
                    v_isSharedCheck_5370_ = (!crate::leanh::lean_is_exclusive(v___x_5334_)) as u8;
                    if v_isSharedCheck_5370_ == 0 {
                        v___x_5365_ = v___x_5334_;
                        v_isShared_5366_ = v_isSharedCheck_5370_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5363_);
                        crate::leanh::lean_dec(v___x_5334_);
                        v___x_5365_ = crate::leanh::lean_box(0);
                        v_isShared_5366_ = v_isSharedCheck_5370_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5338_) == 0 {
                    v_a_5339_ = crate::leanh::lean_ctor_get(v___y_5338_, 0);
                    v_isSharedCheck_5347_ = (!crate::leanh::lean_is_exclusive(v___y_5338_)) as u8;
                    if v_isSharedCheck_5347_ == 0 {
                        v___x_5341_ = v___y_5338_;
                        v_isShared_5342_ = v_isSharedCheck_5347_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5339_);
                        crate::leanh::lean_dec(v___y_5338_);
                        v___x_5341_ = crate::leanh::lean_box(0);
                        v_isShared_5342_ = v_isSharedCheck_5347_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5336_);
                    return v___y_5338_;
                }
            }
            2 => {
                v___x_5343_ = lean_st_ref_get(v___x_5336_);
                crate::leanh::lean_dec(v___x_5336_);
                crate::leanh::lean_dec(v___x_5343_);
                if v_isShared_5342_ == 0 {
                    v___x_5345_ = v___x_5341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5339_);
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
                    v_reuseFailAlloc_5361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
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
                    v_reuseFailAlloc_5369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5363_);
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
    mut v___f_5371_: *mut crate::leanh::LeanObject,
    mut v___f_5372_: *mut crate::leanh::LeanObject,
    mut v___x_5373_: *mut crate::leanh::LeanObject,
    mut v_e_5374_: *mut crate::leanh::LeanObject,
    mut v_candidates_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
    mut v___y_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_17597__boxed_5381_: u8 = 0;
    let mut v_res_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_17597__boxed_5381_ = (crate::leanh::lean_unbox(v___x_5373_) as u8);
    v_res_5382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5371_, v___f_5372_, v___x_17597__boxed_5381_, v_e_5374_, v_candidates_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
    crate::leanh::lean_dec(v___y_5379_);
    crate::leanh::lean_dec_ref(v___y_5378_);
    crate::leanh::lean_dec(v___y_5377_);
    crate::leanh::lean_dec_ref(v___y_5376_);
    return v_res_5382_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(
    mut v_e_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5390_ = lean_st_ref_take(v___y_5384_);
    v___x_5391_ = l_Lean_Expr_fvarId_x21(v_e_5383_);
    v___x_5392_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_5390_, v___x_5391_);
    crate::leanh::lean_dec(v___x_5391_);
    v___x_5393_ = lean_st_ref_set(v___y_5384_, v___x_5392_);
    v___x_5394_ = crate::leanh::lean_box(0);
    v___x_5395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5395_, 0, v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(
    mut v_e_5396_: *mut crate::leanh::LeanObject,
    mut v___y_5397_: *mut crate::leanh::LeanObject,
    mut v___y_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
    mut v___y_5400_: *mut crate::leanh::LeanObject,
    mut v___y_5401_: *mut crate::leanh::LeanObject,
    mut v___y_5402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_e_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
    crate::leanh::lean_dec(v___y_5401_);
    crate::leanh::lean_dec_ref(v___y_5400_);
    crate::leanh::lean_dec(v___y_5399_);
    crate::leanh::lean_dec_ref(v___y_5398_);
    crate::leanh::lean_dec(v___y_5397_);
    crate::leanh::lean_dec_ref(v_e_5396_);
    return v_res_5403_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(
    mut v_____r_5404_: *mut crate::leanh::LeanObject,
    mut v___y_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
    mut v___y_5409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5411_ = lean_st_ref_get(v___y_5405_);
    v___x_5412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5412_, 0, v___x_5411_);
    return v___x_5412_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(
    mut v_____r_5413_: *mut crate::leanh::LeanObject,
    mut v___y_5414_: *mut crate::leanh::LeanObject,
    mut v___y_5415_: *mut crate::leanh::LeanObject,
    mut v___y_5416_: *mut crate::leanh::LeanObject,
    mut v___y_5417_: *mut crate::leanh::LeanObject,
    mut v___y_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_____r_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
    crate::leanh::lean_dec(v___y_5418_);
    crate::leanh::lean_dec_ref(v___y_5417_);
    crate::leanh::lean_dec(v___y_5416_);
    crate::leanh::lean_dec_ref(v___y_5415_);
    crate::leanh::lean_dec(v___y_5414_);
    return v_res_5420_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(
    mut v_x_5421_: *mut crate::leanh::LeanObject,
    mut v_x_5422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5428_: u8 = 0;
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5448_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5422_) == 0 {
                    return v_x_5421_;
                } else {
                    v_key_5423_ = crate::leanh::lean_ctor_get(v_x_5422_, 0);
                    v_value_5424_ = crate::leanh::lean_ctor_get(v_x_5422_, 1);
                    v_tail_5425_ = crate::leanh::lean_ctor_get(v_x_5422_, 2);
                    v_isSharedCheck_5448_ = (!crate::leanh::lean_is_exclusive(v_x_5422_)) as u8;
                    if v_isSharedCheck_5448_ == 0 {
                        v___x_5427_ = v_x_5422_;
                        v_isShared_5428_ = v_isSharedCheck_5448_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5425_);
                        crate::leanh::lean_inc(v_value_5424_);
                        crate::leanh::lean_inc(v_key_5423_);
                        crate::leanh::lean_dec(v_x_5422_);
                        v___x_5427_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_5442_);
                if v_isShared_5428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5427_, 2, v___x_5442_);
                    v___x_5444_ = v___x_5427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5447_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_key_5423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5447_, 1, v_value_5424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5447_, 2, v___x_5442_);
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
    mut v_i_5449_: *mut crate::leanh::LeanObject,
    mut v_source_5450_: *mut crate::leanh::LeanObject,
    mut v_target_5451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: u8 = 0;
    let mut v_es_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5452_ = lean_array_get_size(v_source_5450_);
                v___x_5453_ = lean_nat_dec_lt(v_i_5449_, v___x_5452_);
                if v___x_5453_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5450_);
                    crate::leanh::lean_dec(v_i_5449_);
                    return v_target_5451_;
                } else {
                    v_es_5454_ = lean_array_fget(v_source_5450_, v_i_5449_);
                    v___x_5455_ = crate::leanh::lean_box(0);
                    v_source_5456_ = lean_array_fset(v_source_5450_, v_i_5449_, v___x_5455_);
                    v_target_5457_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_5451_, v_es_5454_);
                    v___x_5458_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5459_ = lean_nat_add(v_i_5449_, v___x_5458_);
                    crate::leanh::lean_dec(v_i_5449_);
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
    mut v_data_5461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5462_ = lean_array_get_size(v_data_5461_);
    v___x_5463_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5464_ = lean_nat_mul(v___x_5462_, v___x_5463_);
    v___x_5465_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5466_ = crate::leanh::lean_box(0);
    v___x_5467_ = lean_mk_array(v_nbuckets_5464_, v___x_5466_);
    v___x_5468_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_5465_, v_data_5461_, v___x_5467_);
    return v___x_5468_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(
    mut v_m_5469_: *mut crate::leanh::LeanObject,
    mut v_a_5470_: *mut crate::leanh::LeanObject,
    mut v_b_5471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: u8 = 0;
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5491_: u8 = 0;
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: u8 = 0;
    let mut v_val_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5509_: u8 = 0;
    let mut v_unused_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5472_ = crate::leanh::lean_ctor_get(v_m_5469_, 0);
                v_buckets_5473_ = crate::leanh::lean_ctor_get(v_m_5469_, 1);
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
                    crate::leanh::lean_inc_ref(v_buckets_5473_);
                    crate::leanh::lean_inc(v_size_5472_);
                    v_isSharedCheck_5509_ = (!crate::leanh::lean_is_exclusive(v_m_5469_)) as u8;
                    if v_isSharedCheck_5509_ == 0 {
                        v_unused_5510_ = crate::leanh::lean_ctor_get(v_m_5469_, 1);
                        crate::leanh::lean_dec(v_unused_5510_);
                        v_unused_5511_ = crate::leanh::lean_ctor_get(v_m_5469_, 0);
                        crate::leanh::lean_dec(v_unused_5511_);
                        v___x_5490_ = v_m_5469_;
                        v_isShared_5491_ = v_isSharedCheck_5509_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_5469_);
                        v___x_5490_ = crate::leanh::lean_box(0);
                        v_isShared_5491_ = v_isSharedCheck_5509_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_5471_);
                    crate::leanh::lean_dec(v_a_5470_);
                    return v_m_5469_;
                }
            }
            1 => {
                v___x_5492_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_5493_ = lean_nat_add(v_size_5472_, v___x_5492_);
                crate::leanh::lean_dec(v_size_5472_);
                crate::leanh::lean_inc(v_bkt_5487_);
                v___x_5494_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5494_, 0, v_a_5470_);
                crate::leanh::lean_ctor_set(v___x_5494_, 1, v_b_5471_);
                crate::leanh::lean_ctor_set(v___x_5494_, 2, v_bkt_5487_);
                v_buckets_x27_5495_ = lean_array_uset(v_buckets_5473_, v___x_5486_, v___x_5494_);
                v___x_5496_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_5497_ = lean_nat_mul(v_size_x27_5493_, v___x_5496_);
                v___x_5498_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5499_ = lean_nat_div(v___x_5497_, v___x_5498_);
                crate::leanh::lean_dec(v___x_5497_);
                v___x_5500_ = lean_array_get_size(v_buckets_x27_5495_);
                v___x_5501_ = lean_nat_dec_le(v___x_5499_, v___x_5500_);
                crate::leanh::lean_dec(v___x_5499_);
                if v___x_5501_ == 0 {
                    v_val_5502_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_5495_);
                    if v_isShared_5491_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5490_, 1, v_val_5502_);
                        crate::leanh::lean_ctor_set(v___x_5490_, 0, v_size_x27_5493_);
                        v___x_5504_ = v___x_5490_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_size_x27_5493_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_val_5502_);
                        v___x_5504_ = v_reuseFailAlloc_5505_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5491_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5490_, 1, v_buckets_x27_5495_);
                        crate::leanh::lean_ctor_set(v___x_5490_, 0, v_size_x27_5493_);
                        v___x_5507_ = v___x_5490_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_size_x27_5493_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5508_, 1, v_buckets_x27_5495_);
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
    mut v_as_5514_: *mut crate::leanh::LeanObject,
    mut v_sz_5515_: usize,
    mut v_i_5516_: usize,
    mut v_b_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
    mut v___y_5519_: *mut crate::leanh::LeanObject,
    mut v___y_5520_: *mut crate::leanh::LeanObject,
    mut v___y_5521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5523_: u8 = 0;
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: usize = 0;
    let mut v___x_5535_: usize = 0;
    let mut v_reuseFailAlloc_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: u8 = 0;
    let mut v___f_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: u8 = 0;
    let mut v_a_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5576_: u8 = 0;
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_a_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5584_: u8 = 0;
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_unused_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5523_ = lean_usize_dec_lt(v_i_5516_, v_sz_5515_);
                if v___x_5523_ == 0 {
                    v___x_5524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5524_, 0, v_b_5517_);
                    return v___x_5524_;
                } else {
                    v_snd_5525_ = crate::leanh::lean_ctor_get(v_b_5517_, 1);
                    v_isSharedCheck_5589_ = (!crate::leanh::lean_is_exclusive(v_b_5517_)) as u8;
                    if v_isSharedCheck_5589_ == 0 {
                        v_unused_5590_ = crate::leanh::lean_ctor_get(v_b_5517_, 0);
                        crate::leanh::lean_dec(v_unused_5590_);
                        v___x_5527_ = v_b_5517_;
                        v_isShared_5528_ = v_isSharedCheck_5589_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5525_);
                        crate::leanh::lean_dec(v_b_5517_);
                        v___x_5527_ = crate::leanh::lean_box(0);
                        v_isShared_5528_ = v_isSharedCheck_5589_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5529_ = crate::leanh::lean_box(0);
                v_a_5538_ = lean_array_uget_borrowed(v_as_5514_, v_i_5516_);
                if crate::leanh::lean_obj_tag(v_a_5538_) == 0 {
                    v_a_5531_ = v_snd_5525_;
                    state = 2;
                    continue;
                } else {
                    v_val_5539_ = crate::leanh::lean_ctor_get(v_a_5538_, 0);
                    v___x_5545_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5539_);
                    if v___x_5545_ == 0 {
                        v___f_5546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5548_ = l_Lean_LocalDecl_type(v_val_5539_);
                        crate::leanh::lean_inc_ref(v___x_5548_);
                        v___x_5567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5547_, v___f_5546_, v___x_5545_, v___x_5548_, v_snd_5525_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
                        if crate::leanh::lean_obj_tag(v___x_5567_) == 0 {
                            v_a_5568_ = crate::leanh::lean_ctor_get(v___x_5567_, 0);
                            crate::leanh::lean_inc(v_a_5568_);
                            crate::leanh::lean_dec_ref_known(v___x_5567_, 1);
                            v___x_5569_ = l_Lean_LocalDecl_value_x3f(v_val_5539_, v___x_5545_);
                            if crate::leanh::lean_obj_tag(v___x_5569_) == 0 {
                                v_candidates_5550_ = v_a_5568_;
                                v___y_5551_ = v___y_5518_;
                                v___y_5552_ = v___y_5519_;
                                v___y_5553_ = v___y_5520_;
                                v___y_5554_ = v___y_5521_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5570_ = crate::leanh::lean_ctor_get(v___x_5569_, 0);
                                crate::leanh::lean_inc(v_val_5570_);
                                crate::leanh::lean_dec_ref_known(v___x_5569_, 1);
                                v___x_5571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5547_, v___f_5546_, v___x_5545_, v_val_5570_, v_a_5568_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
                                if crate::leanh::lean_obj_tag(v___x_5571_) == 0 {
                                    v_a_5572_ = crate::leanh::lean_ctor_get(v___x_5571_, 0);
                                    crate::leanh::lean_inc(v_a_5572_);
                                    crate::leanh::lean_dec_ref_known(v___x_5571_, 1);
                                    v_candidates_5550_ = v_a_5572_;
                                    v___y_5551_ = v___y_5518_;
                                    v___y_5552_ = v___y_5519_;
                                    v___y_5553_ = v___y_5520_;
                                    v___y_5554_ = v___y_5521_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5548_);
                                    crate::leanh::lean_del_object(v___x_5527_);
                                    v_a_5573_ = crate::leanh::lean_ctor_get(v___x_5571_, 0);
                                    v_isSharedCheck_5580_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5571_)) as u8;
                                    if v_isSharedCheck_5580_ == 0 {
                                        v___x_5575_ = v___x_5571_;
                                        v_isShared_5576_ = v_isSharedCheck_5580_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5573_);
                                        crate::leanh::lean_dec(v___x_5571_);
                                        v___x_5575_ = crate::leanh::lean_box(0);
                                        v_isShared_5576_ = v_isSharedCheck_5580_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5548_);
                            crate::leanh::lean_del_object(v___x_5527_);
                            v_a_5581_ = crate::leanh::lean_ctor_get(v___x_5567_, 0);
                            v_isSharedCheck_5588_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5567_)) as u8;
                            if v_isSharedCheck_5588_ == 0 {
                                v___x_5583_ = v___x_5567_;
                                v_isShared_5584_ = v_isSharedCheck_5588_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5581_);
                                crate::leanh::lean_dec(v___x_5567_);
                                v___x_5583_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_5527_, 1, v_a_5531_);
                    crate::leanh::lean_ctor_set(v___x_5527_, 0, v___x_5529_);
                    v___x_5533_ = v___x_5527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5537_, 0, v___x_5529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5537_, 1, v_a_5531_);
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
                v___x_5543_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_5555_) == 0 {
                    v_a_5556_ = crate::leanh::lean_ctor_get(v___x_5555_, 0);
                    crate::leanh::lean_inc(v_a_5556_);
                    crate::leanh::lean_dec_ref_known(v___x_5555_, 1);
                    v___x_5557_ = (crate::leanh::lean_unbox(v_a_5556_) as u8);
                    crate::leanh::lean_dec(v_a_5556_);
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
                    crate::leanh::lean_dec_ref(v_candidates_5550_);
                    crate::leanh::lean_del_object(v___x_5527_);
                    v_a_5559_ = crate::leanh::lean_ctor_get(v___x_5555_, 0);
                    v_isSharedCheck_5566_ = (!crate::leanh::lean_is_exclusive(v___x_5555_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v___x_5561_ = v___x_5555_;
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5559_);
                        crate::leanh::lean_dec(v___x_5555_);
                        v___x_5561_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
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
                    v_reuseFailAlloc_5579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
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
                    v_reuseFailAlloc_5587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
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
    mut v_as_5591_: *mut crate::leanh::LeanObject,
    mut v_sz_5592_: *mut crate::leanh::LeanObject,
    mut v_i_5593_: *mut crate::leanh::LeanObject,
    mut v_b_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
    mut v___y_5597_: *mut crate::leanh::LeanObject,
    mut v___y_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5600_: usize = 0;
    let mut v_i_boxed_5601_: usize = 0;
    let mut v_res_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5600_ = crate::leanh::lean_unbox_usize(v_sz_5592_);
    crate::leanh::lean_dec(v_sz_5592_);
    v_i_boxed_5601_ = crate::leanh::lean_unbox_usize(v_i_5593_);
    crate::leanh::lean_dec(v_i_5593_);
    v_res_5602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_5591_, v_sz_boxed_5600_, v_i_boxed_5601_, v_b_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    crate::leanh::lean_dec(v___y_5598_);
    crate::leanh::lean_dec_ref(v___y_5597_);
    crate::leanh::lean_dec(v___y_5596_);
    crate::leanh::lean_dec_ref(v___y_5595_);
    crate::leanh::lean_dec_ref(v_as_5591_);
    return v_res_5602_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(
    mut v_as_5603_: *mut crate::leanh::LeanObject,
    mut v_sz_5604_: usize,
    mut v_i_5605_: usize,
    mut v_b_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5612_: u8 = 0;
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: usize = 0;
    let mut v___x_5624_: usize = 0;
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: u8 = 0;
    let mut v___f_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: u8 = 0;
    let mut v___x_5647_: u8 = 0;
    let mut v_a_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5651_: u8 = 0;
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5655_: u8 = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5669_: u8 = 0;
    let mut v_a_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5673_: u8 = 0;
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut v_unused_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5612_ = lean_usize_dec_lt(v_i_5605_, v_sz_5604_);
                if v___x_5612_ == 0 {
                    v___x_5613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5613_, 0, v_b_5606_);
                    return v___x_5613_;
                } else {
                    v_snd_5614_ = crate::leanh::lean_ctor_get(v_b_5606_, 1);
                    v_isSharedCheck_5678_ = (!crate::leanh::lean_is_exclusive(v_b_5606_)) as u8;
                    if v_isSharedCheck_5678_ == 0 {
                        v_unused_5679_ = crate::leanh::lean_ctor_get(v_b_5606_, 0);
                        crate::leanh::lean_dec(v_unused_5679_);
                        v___x_5616_ = v_b_5606_;
                        v_isShared_5617_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5614_);
                        crate::leanh::lean_dec(v_b_5606_);
                        v___x_5616_ = crate::leanh::lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5618_ = crate::leanh::lean_box(0);
                v_a_5627_ = lean_array_uget_borrowed(v_as_5603_, v_i_5605_);
                if crate::leanh::lean_obj_tag(v_a_5627_) == 0 {
                    v_a_5620_ = v_snd_5614_;
                    state = 2;
                    continue;
                } else {
                    v_val_5628_ = crate::leanh::lean_ctor_get(v_a_5627_, 0);
                    v___x_5634_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5628_);
                    if v___x_5634_ == 0 {
                        v___f_5635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5637_ = l_Lean_LocalDecl_type(v_val_5628_);
                        crate::leanh::lean_inc_ref(v___x_5637_);
                        v___x_5656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5636_, v___f_5635_, v___x_5634_, v___x_5637_, v_snd_5614_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
                        if crate::leanh::lean_obj_tag(v___x_5656_) == 0 {
                            v_a_5657_ = crate::leanh::lean_ctor_get(v___x_5656_, 0);
                            crate::leanh::lean_inc(v_a_5657_);
                            crate::leanh::lean_dec_ref_known(v___x_5656_, 1);
                            v___x_5658_ = l_Lean_LocalDecl_value_x3f(v_val_5628_, v___x_5634_);
                            if crate::leanh::lean_obj_tag(v___x_5658_) == 0 {
                                v_candidates_5639_ = v_a_5657_;
                                v___y_5640_ = v___y_5607_;
                                v___y_5641_ = v___y_5608_;
                                v___y_5642_ = v___y_5609_;
                                v___y_5643_ = v___y_5610_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5659_ = crate::leanh::lean_ctor_get(v___x_5658_, 0);
                                crate::leanh::lean_inc(v_val_5659_);
                                crate::leanh::lean_dec_ref_known(v___x_5658_, 1);
                                v___x_5660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5636_, v___f_5635_, v___x_5634_, v_val_5659_, v_a_5657_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
                                if crate::leanh::lean_obj_tag(v___x_5660_) == 0 {
                                    v_a_5661_ = crate::leanh::lean_ctor_get(v___x_5660_, 0);
                                    crate::leanh::lean_inc(v_a_5661_);
                                    crate::leanh::lean_dec_ref_known(v___x_5660_, 1);
                                    v_candidates_5639_ = v_a_5661_;
                                    v___y_5640_ = v___y_5607_;
                                    v___y_5641_ = v___y_5608_;
                                    v___y_5642_ = v___y_5609_;
                                    v___y_5643_ = v___y_5610_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5637_);
                                    crate::leanh::lean_del_object(v___x_5616_);
                                    v_a_5662_ = crate::leanh::lean_ctor_get(v___x_5660_, 0);
                                    v_isSharedCheck_5669_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5660_)) as u8;
                                    if v_isSharedCheck_5669_ == 0 {
                                        v___x_5664_ = v___x_5660_;
                                        v_isShared_5665_ = v_isSharedCheck_5669_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5662_);
                                        crate::leanh::lean_dec(v___x_5660_);
                                        v___x_5664_ = crate::leanh::lean_box(0);
                                        v_isShared_5665_ = v_isSharedCheck_5669_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5637_);
                            crate::leanh::lean_del_object(v___x_5616_);
                            v_a_5670_ = crate::leanh::lean_ctor_get(v___x_5656_, 0);
                            v_isSharedCheck_5677_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5656_)) as u8;
                            if v_isSharedCheck_5677_ == 0 {
                                v___x_5672_ = v___x_5656_;
                                v_isShared_5673_ = v_isSharedCheck_5677_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5670_);
                                crate::leanh::lean_dec(v___x_5656_);
                                v___x_5672_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_5616_, 1, v_a_5620_);
                    crate::leanh::lean_ctor_set(v___x_5616_, 0, v___x_5618_);
                    v___x_5622_ = v___x_5616_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5626_, 0, v___x_5618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5626_, 1, v_a_5620_);
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
                v___x_5632_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_5644_) == 0 {
                    v_a_5645_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                    crate::leanh::lean_inc(v_a_5645_);
                    crate::leanh::lean_dec_ref_known(v___x_5644_, 1);
                    v___x_5646_ = (crate::leanh::lean_unbox(v_a_5645_) as u8);
                    crate::leanh::lean_dec(v_a_5645_);
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
                    crate::leanh::lean_dec_ref(v_candidates_5639_);
                    crate::leanh::lean_del_object(v___x_5616_);
                    v_a_5648_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                    v_isSharedCheck_5655_ = (!crate::leanh::lean_is_exclusive(v___x_5644_)) as u8;
                    if v_isSharedCheck_5655_ == 0 {
                        v___x_5650_ = v___x_5644_;
                        v_isShared_5651_ = v_isSharedCheck_5655_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5648_);
                        crate::leanh::lean_dec(v___x_5644_);
                        v___x_5650_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_a_5648_);
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
                    v_reuseFailAlloc_5668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5662_);
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
                    v_reuseFailAlloc_5676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_a_5670_);
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
    mut v_as_5680_: *mut crate::leanh::LeanObject,
    mut v_sz_5681_: *mut crate::leanh::LeanObject,
    mut v_i_5682_: *mut crate::leanh::LeanObject,
    mut v_b_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5689_: usize = 0;
    let mut v_i_boxed_5690_: usize = 0;
    let mut v_res_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5689_ = crate::leanh::lean_unbox_usize(v_sz_5681_);
    crate::leanh::lean_dec(v_sz_5681_);
    v_i_boxed_5690_ = crate::leanh::lean_unbox_usize(v_i_5682_);
    crate::leanh::lean_dec(v_i_5682_);
    v_res_5691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_5680_, v_sz_boxed_5689_, v_i_boxed_5690_, v_b_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
    crate::leanh::lean_dec(v___y_5687_);
    crate::leanh::lean_dec_ref(v___y_5686_);
    crate::leanh::lean_dec(v___y_5685_);
    crate::leanh::lean_dec_ref(v___y_5684_);
    crate::leanh::lean_dec_ref(v_as_5680_);
    return v_res_5691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(
    mut v_as_5692_: *mut crate::leanh::LeanObject,
    mut v_sz_5693_: usize,
    mut v_i_5694_: usize,
    mut v_b_5695_: *mut crate::leanh::LeanObject,
    mut v___y_5696_: *mut crate::leanh::LeanObject,
    mut v___y_5697_: *mut crate::leanh::LeanObject,
    mut v___y_5698_: *mut crate::leanh::LeanObject,
    mut v___y_5699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5701_: u8 = 0;
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5706_: u8 = 0;
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: usize = 0;
    let mut v___x_5713_: usize = 0;
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: u8 = 0;
    let mut v___f_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u8 = 0;
    let mut v___x_5736_: u8 = 0;
    let mut v_a_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5754_: u8 = 0;
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5758_: u8 = 0;
    let mut v_a_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_isSharedCheck_5767_: u8 = 0;
    let mut v_unused_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5701_ = lean_usize_dec_lt(v_i_5694_, v_sz_5693_);
                if v___x_5701_ == 0 {
                    v___x_5702_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5702_, 0, v_b_5695_);
                    return v___x_5702_;
                } else {
                    v_snd_5703_ = crate::leanh::lean_ctor_get(v_b_5695_, 1);
                    v_isSharedCheck_5767_ = (!crate::leanh::lean_is_exclusive(v_b_5695_)) as u8;
                    if v_isSharedCheck_5767_ == 0 {
                        v_unused_5768_ = crate::leanh::lean_ctor_get(v_b_5695_, 0);
                        crate::leanh::lean_dec(v_unused_5768_);
                        v___x_5705_ = v_b_5695_;
                        v_isShared_5706_ = v_isSharedCheck_5767_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5703_);
                        crate::leanh::lean_dec(v_b_5695_);
                        v___x_5705_ = crate::leanh::lean_box(0);
                        v_isShared_5706_ = v_isSharedCheck_5767_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5707_ = crate::leanh::lean_box(0);
                v_a_5716_ = lean_array_uget_borrowed(v_as_5692_, v_i_5694_);
                if crate::leanh::lean_obj_tag(v_a_5716_) == 0 {
                    v_a_5709_ = v_snd_5703_;
                    state = 2;
                    continue;
                } else {
                    v_val_5717_ = crate::leanh::lean_ctor_get(v_a_5716_, 0);
                    v___x_5723_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5717_);
                    if v___x_5723_ == 0 {
                        v___f_5724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5726_ = l_Lean_LocalDecl_type(v_val_5717_);
                        crate::leanh::lean_inc_ref(v___x_5726_);
                        v___x_5745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5725_, v___f_5724_, v___x_5723_, v___x_5726_, v_snd_5703_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
                        if crate::leanh::lean_obj_tag(v___x_5745_) == 0 {
                            v_a_5746_ = crate::leanh::lean_ctor_get(v___x_5745_, 0);
                            crate::leanh::lean_inc(v_a_5746_);
                            crate::leanh::lean_dec_ref_known(v___x_5745_, 1);
                            v___x_5747_ = l_Lean_LocalDecl_value_x3f(v_val_5717_, v___x_5723_);
                            if crate::leanh::lean_obj_tag(v___x_5747_) == 0 {
                                v_candidates_5728_ = v_a_5746_;
                                v___y_5729_ = v___y_5696_;
                                v___y_5730_ = v___y_5697_;
                                v___y_5731_ = v___y_5698_;
                                v___y_5732_ = v___y_5699_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5748_ = crate::leanh::lean_ctor_get(v___x_5747_, 0);
                                crate::leanh::lean_inc(v_val_5748_);
                                crate::leanh::lean_dec_ref_known(v___x_5747_, 1);
                                v___x_5749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5725_, v___f_5724_, v___x_5723_, v_val_5748_, v_a_5746_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
                                if crate::leanh::lean_obj_tag(v___x_5749_) == 0 {
                                    v_a_5750_ = crate::leanh::lean_ctor_get(v___x_5749_, 0);
                                    crate::leanh::lean_inc(v_a_5750_);
                                    crate::leanh::lean_dec_ref_known(v___x_5749_, 1);
                                    v_candidates_5728_ = v_a_5750_;
                                    v___y_5729_ = v___y_5696_;
                                    v___y_5730_ = v___y_5697_;
                                    v___y_5731_ = v___y_5698_;
                                    v___y_5732_ = v___y_5699_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5726_);
                                    crate::leanh::lean_del_object(v___x_5705_);
                                    v_a_5751_ = crate::leanh::lean_ctor_get(v___x_5749_, 0);
                                    v_isSharedCheck_5758_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5749_)) as u8;
                                    if v_isSharedCheck_5758_ == 0 {
                                        v___x_5753_ = v___x_5749_;
                                        v_isShared_5754_ = v_isSharedCheck_5758_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5751_);
                                        crate::leanh::lean_dec(v___x_5749_);
                                        v___x_5753_ = crate::leanh::lean_box(0);
                                        v_isShared_5754_ = v_isSharedCheck_5758_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5726_);
                            crate::leanh::lean_del_object(v___x_5705_);
                            v_a_5759_ = crate::leanh::lean_ctor_get(v___x_5745_, 0);
                            v_isSharedCheck_5766_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5745_)) as u8;
                            if v_isSharedCheck_5766_ == 0 {
                                v___x_5761_ = v___x_5745_;
                                v_isShared_5762_ = v_isSharedCheck_5766_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5759_);
                                crate::leanh::lean_dec(v___x_5745_);
                                v___x_5761_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_5705_, 1, v_a_5709_);
                    crate::leanh::lean_ctor_set(v___x_5705_, 0, v___x_5707_);
                    v___x_5711_ = v___x_5705_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 1, v_a_5709_);
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
                v___x_5721_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_5733_) == 0 {
                    v_a_5734_ = crate::leanh::lean_ctor_get(v___x_5733_, 0);
                    crate::leanh::lean_inc(v_a_5734_);
                    crate::leanh::lean_dec_ref_known(v___x_5733_, 1);
                    v___x_5735_ = (crate::leanh::lean_unbox(v_a_5734_) as u8);
                    crate::leanh::lean_dec(v_a_5734_);
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
                    crate::leanh::lean_dec_ref(v_candidates_5728_);
                    crate::leanh::lean_del_object(v___x_5705_);
                    v_a_5737_ = crate::leanh::lean_ctor_get(v___x_5733_, 0);
                    v_isSharedCheck_5744_ = (!crate::leanh::lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5744_ == 0 {
                        v___x_5739_ = v___x_5733_;
                        v_isShared_5740_ = v_isSharedCheck_5744_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5737_);
                        crate::leanh::lean_dec(v___x_5733_);
                        v___x_5739_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
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
                    v_reuseFailAlloc_5757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
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
                    v_reuseFailAlloc_5765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
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
    mut v_as_5769_: *mut crate::leanh::LeanObject,
    mut v_sz_5770_: *mut crate::leanh::LeanObject,
    mut v_i_5771_: *mut crate::leanh::LeanObject,
    mut v_b_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
    mut v___y_5775_: *mut crate::leanh::LeanObject,
    mut v___y_5776_: *mut crate::leanh::LeanObject,
    mut v___y_5777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5778_: usize = 0;
    let mut v_i_boxed_5779_: usize = 0;
    let mut v_res_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5778_ = crate::leanh::lean_unbox_usize(v_sz_5770_);
    crate::leanh::lean_dec(v_sz_5770_);
    v_i_boxed_5779_ = crate::leanh::lean_unbox_usize(v_i_5771_);
    crate::leanh::lean_dec(v_i_5771_);
    v_res_5780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_5769_, v_sz_boxed_5778_, v_i_boxed_5779_, v_b_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
    crate::leanh::lean_dec(v___y_5776_);
    crate::leanh::lean_dec_ref(v___y_5775_);
    crate::leanh::lean_dec(v___y_5774_);
    crate::leanh::lean_dec_ref(v___y_5773_);
    crate::leanh::lean_dec_ref(v_as_5769_);
    return v_res_5780_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(
    mut v_as_5781_: *mut crate::leanh::LeanObject,
    mut v_sz_5782_: usize,
    mut v_i_5783_: usize,
    mut v_b_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
    mut v___y_5786_: *mut crate::leanh::LeanObject,
    mut v___y_5787_: *mut crate::leanh::LeanObject,
    mut v___y_5788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: usize = 0;
    let mut v___x_5802_: usize = 0;
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: u8 = 0;
    let mut v___f_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v___x_5825_: u8 = 0;
    let mut v_a_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5847_: u8 = 0;
    let mut v_a_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5851_: u8 = 0;
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_isSharedCheck_5856_: u8 = 0;
    let mut v_unused_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5790_ = lean_usize_dec_lt(v_i_5783_, v_sz_5782_);
                if v___x_5790_ == 0 {
                    v___x_5791_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5791_, 0, v_b_5784_);
                    return v___x_5791_;
                } else {
                    v_snd_5792_ = crate::leanh::lean_ctor_get(v_b_5784_, 1);
                    v_isSharedCheck_5856_ = (!crate::leanh::lean_is_exclusive(v_b_5784_)) as u8;
                    if v_isSharedCheck_5856_ == 0 {
                        v_unused_5857_ = crate::leanh::lean_ctor_get(v_b_5784_, 0);
                        crate::leanh::lean_dec(v_unused_5857_);
                        v___x_5794_ = v_b_5784_;
                        v_isShared_5795_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5792_);
                        crate::leanh::lean_dec(v_b_5784_);
                        v___x_5794_ = crate::leanh::lean_box(0);
                        v_isShared_5795_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5796_ = crate::leanh::lean_box(0);
                v_a_5805_ = lean_array_uget_borrowed(v_as_5781_, v_i_5783_);
                if crate::leanh::lean_obj_tag(v_a_5805_) == 0 {
                    v_a_5798_ = v_snd_5792_;
                    state = 2;
                    continue;
                } else {
                    v_val_5806_ = crate::leanh::lean_ctor_get(v_a_5805_, 0);
                    v___x_5812_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5806_);
                    if v___x_5812_ == 0 {
                        v___f_5813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5815_ = l_Lean_LocalDecl_type(v_val_5806_);
                        crate::leanh::lean_inc_ref(v___x_5815_);
                        v___x_5834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5814_, v___f_5813_, v___x_5812_, v___x_5815_, v_snd_5792_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
                        if crate::leanh::lean_obj_tag(v___x_5834_) == 0 {
                            v_a_5835_ = crate::leanh::lean_ctor_get(v___x_5834_, 0);
                            crate::leanh::lean_inc(v_a_5835_);
                            crate::leanh::lean_dec_ref_known(v___x_5834_, 1);
                            v___x_5836_ = l_Lean_LocalDecl_value_x3f(v_val_5806_, v___x_5812_);
                            if crate::leanh::lean_obj_tag(v___x_5836_) == 0 {
                                v_candidates_5817_ = v_a_5835_;
                                v___y_5818_ = v___y_5785_;
                                v___y_5819_ = v___y_5786_;
                                v___y_5820_ = v___y_5787_;
                                v___y_5821_ = v___y_5788_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5837_ = crate::leanh::lean_ctor_get(v___x_5836_, 0);
                                crate::leanh::lean_inc(v_val_5837_);
                                crate::leanh::lean_dec_ref_known(v___x_5836_, 1);
                                v___x_5838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5814_, v___f_5813_, v___x_5812_, v_val_5837_, v_a_5835_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
                                if crate::leanh::lean_obj_tag(v___x_5838_) == 0 {
                                    v_a_5839_ = crate::leanh::lean_ctor_get(v___x_5838_, 0);
                                    crate::leanh::lean_inc(v_a_5839_);
                                    crate::leanh::lean_dec_ref_known(v___x_5838_, 1);
                                    v_candidates_5817_ = v_a_5839_;
                                    v___y_5818_ = v___y_5785_;
                                    v___y_5819_ = v___y_5786_;
                                    v___y_5820_ = v___y_5787_;
                                    v___y_5821_ = v___y_5788_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5815_);
                                    crate::leanh::lean_del_object(v___x_5794_);
                                    v_a_5840_ = crate::leanh::lean_ctor_get(v___x_5838_, 0);
                                    v_isSharedCheck_5847_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5838_)) as u8;
                                    if v_isSharedCheck_5847_ == 0 {
                                        v___x_5842_ = v___x_5838_;
                                        v_isShared_5843_ = v_isSharedCheck_5847_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5840_);
                                        crate::leanh::lean_dec(v___x_5838_);
                                        v___x_5842_ = crate::leanh::lean_box(0);
                                        v_isShared_5843_ = v_isSharedCheck_5847_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5815_);
                            crate::leanh::lean_del_object(v___x_5794_);
                            v_a_5848_ = crate::leanh::lean_ctor_get(v___x_5834_, 0);
                            v_isSharedCheck_5855_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5834_)) as u8;
                            if v_isSharedCheck_5855_ == 0 {
                                v___x_5850_ = v___x_5834_;
                                v_isShared_5851_ = v_isSharedCheck_5855_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5848_);
                                crate::leanh::lean_dec(v___x_5834_);
                                v___x_5850_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_5794_, 1, v_a_5798_);
                    crate::leanh::lean_ctor_set(v___x_5794_, 0, v___x_5796_);
                    v___x_5800_ = v___x_5794_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5804_, 0, v___x_5796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5804_, 1, v_a_5798_);
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
                v___x_5810_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_5822_) == 0 {
                    v_a_5823_ = crate::leanh::lean_ctor_get(v___x_5822_, 0);
                    crate::leanh::lean_inc(v_a_5823_);
                    crate::leanh::lean_dec_ref_known(v___x_5822_, 1);
                    v___x_5824_ = (crate::leanh::lean_unbox(v_a_5823_) as u8);
                    crate::leanh::lean_dec(v_a_5823_);
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
                    crate::leanh::lean_dec_ref(v_candidates_5817_);
                    crate::leanh::lean_del_object(v___x_5794_);
                    v_a_5826_ = crate::leanh::lean_ctor_get(v___x_5822_, 0);
                    v_isSharedCheck_5833_ = (!crate::leanh::lean_is_exclusive(v___x_5822_)) as u8;
                    if v_isSharedCheck_5833_ == 0 {
                        v___x_5828_ = v___x_5822_;
                        v_isShared_5829_ = v_isSharedCheck_5833_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5826_);
                        crate::leanh::lean_dec(v___x_5822_);
                        v___x_5828_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
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
                    v_reuseFailAlloc_5846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_a_5840_);
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
                    v_reuseFailAlloc_5854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_a_5848_);
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
    mut v_as_5858_: *mut crate::leanh::LeanObject,
    mut v_sz_5859_: *mut crate::leanh::LeanObject,
    mut v_i_5860_: *mut crate::leanh::LeanObject,
    mut v_b_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
    mut v___y_5866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5867_: usize = 0;
    let mut v_i_boxed_5868_: usize = 0;
    let mut v_res_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5867_ = crate::leanh::lean_unbox_usize(v_sz_5859_);
    crate::leanh::lean_dec(v_sz_5859_);
    v_i_boxed_5868_ = crate::leanh::lean_unbox_usize(v_i_5860_);
    crate::leanh::lean_dec(v_i_5860_);
    v_res_5869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_5858_, v_sz_boxed_5867_, v_i_boxed_5868_, v_b_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_);
    crate::leanh::lean_dec(v___y_5865_);
    crate::leanh::lean_dec_ref(v___y_5864_);
    crate::leanh::lean_dec(v___y_5863_);
    crate::leanh::lean_dec_ref(v___y_5862_);
    crate::leanh::lean_dec_ref(v_as_5858_);
    return v_res_5869_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(
    mut v_init_5870_: *mut crate::leanh::LeanObject,
    mut v_n_5871_: *mut crate::leanh::LeanObject,
    mut v_b_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
    mut v___y_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5881_: usize = 0;
    let mut v___x_5882_: usize = 0;
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v_fst_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5898_: u8 = 0;
    let mut v_a_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5902_: u8 = 0;
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut v_vs_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5910_: usize = 0;
    let mut v___x_5911_: usize = 0;
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v_fst_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_a_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_5871_) == 0 {
                    v_cs_5878_ = crate::leanh::lean_ctor_get(v_n_5871_, 0);
                    v___x_5879_ = crate::leanh::lean_box(0);
                    v___x_5880_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5880_, 0, v___x_5879_);
                    crate::leanh::lean_ctor_set(v___x_5880_, 1, v_b_5872_);
                    v_sz_5881_ = lean_array_size(v_cs_5878_);
                    v___x_5882_ = 0usize;
                    v___x_5883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_5870_, v_cs_5878_, v_sz_5881_, v___x_5882_, v___x_5880_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
                    if crate::leanh::lean_obj_tag(v___x_5883_) == 0 {
                        v_a_5884_ = crate::leanh::lean_ctor_get(v___x_5883_, 0);
                        v_isSharedCheck_5898_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5883_)) as u8;
                        if v_isSharedCheck_5898_ == 0 {
                            v___x_5886_ = v___x_5883_;
                            v_isShared_5887_ = v_isSharedCheck_5898_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5884_);
                            crate::leanh::lean_dec(v___x_5883_);
                            v___x_5886_ = crate::leanh::lean_box(0);
                            v_isShared_5887_ = v_isSharedCheck_5898_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5899_ = crate::leanh::lean_ctor_get(v___x_5883_, 0);
                        v_isSharedCheck_5906_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5883_)) as u8;
                        if v_isSharedCheck_5906_ == 0 {
                            v___x_5901_ = v___x_5883_;
                            v_isShared_5902_ = v_isSharedCheck_5906_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5899_);
                            crate::leanh::lean_dec(v___x_5883_);
                            v___x_5901_ = crate::leanh::lean_box(0);
                            v_isShared_5902_ = v_isSharedCheck_5906_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5907_ = crate::leanh::lean_ctor_get(v_n_5871_, 0);
                    v___x_5908_ = crate::leanh::lean_box(0);
                    v___x_5909_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5909_, 0, v___x_5908_);
                    crate::leanh::lean_ctor_set(v___x_5909_, 1, v_b_5872_);
                    v_sz_5910_ = lean_array_size(v_vs_5907_);
                    v___x_5911_ = 0usize;
                    v___x_5912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_5907_, v_sz_5910_, v___x_5911_, v___x_5909_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
                    if crate::leanh::lean_obj_tag(v___x_5912_) == 0 {
                        v_a_5913_ = crate::leanh::lean_ctor_get(v___x_5912_, 0);
                        v_isSharedCheck_5927_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5912_)) as u8;
                        if v_isSharedCheck_5927_ == 0 {
                            v___x_5915_ = v___x_5912_;
                            v_isShared_5916_ = v_isSharedCheck_5927_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5913_);
                            crate::leanh::lean_dec(v___x_5912_);
                            v___x_5915_ = crate::leanh::lean_box(0);
                            v_isShared_5916_ = v_isSharedCheck_5927_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5928_ = crate::leanh::lean_ctor_get(v___x_5912_, 0);
                        v_isSharedCheck_5935_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5912_)) as u8;
                        if v_isSharedCheck_5935_ == 0 {
                            v___x_5930_ = v___x_5912_;
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5928_);
                            crate::leanh::lean_dec(v___x_5912_);
                            v___x_5930_ = crate::leanh::lean_box(0);
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5888_ = crate::leanh::lean_ctor_get(v_a_5884_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5888_) == 0 {
                    v_snd_5889_ = crate::leanh::lean_ctor_get(v_a_5884_, 1);
                    crate::leanh::lean_inc(v_snd_5889_);
                    crate::leanh::lean_dec(v_a_5884_);
                    v___x_5890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5890_, 0, v_snd_5889_);
                    if v_isShared_5887_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5886_, 0, v___x_5890_);
                        v___x_5892_ = v___x_5886_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5890_);
                        v___x_5892_ = v_reuseFailAlloc_5893_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5888_);
                    crate::leanh::lean_dec(v_a_5884_);
                    v_val_5894_ = crate::leanh::lean_ctor_get(v_fst_5888_, 0);
                    crate::leanh::lean_inc(v_val_5894_);
                    crate::leanh::lean_dec_ref_known(v_fst_5888_, 1);
                    if v_isShared_5887_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5886_, 0, v_val_5894_);
                        v___x_5896_ = v___x_5886_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_val_5894_);
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
                    v_reuseFailAlloc_5905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
                    v___x_5904_ = v_reuseFailAlloc_5905_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5904_;
            }
            6 => {
                v_fst_5917_ = crate::leanh::lean_ctor_get(v_a_5913_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5917_) == 0 {
                    v_snd_5918_ = crate::leanh::lean_ctor_get(v_a_5913_, 1);
                    crate::leanh::lean_inc(v_snd_5918_);
                    crate::leanh::lean_dec(v_a_5913_);
                    v___x_5919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5919_, 0, v_snd_5918_);
                    if v_isShared_5916_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5915_, 0, v___x_5919_);
                        v___x_5921_ = v___x_5915_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5919_);
                        v___x_5921_ = v_reuseFailAlloc_5922_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5917_);
                    crate::leanh::lean_dec(v_a_5913_);
                    v_val_5923_ = crate::leanh::lean_ctor_get(v_fst_5917_, 0);
                    crate::leanh::lean_inc(v_val_5923_);
                    crate::leanh::lean_dec_ref_known(v_fst_5917_, 1);
                    if v_isShared_5916_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5915_, 0, v_val_5923_);
                        v___x_5925_ = v___x_5915_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_val_5923_);
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
                    v_reuseFailAlloc_5934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
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
    mut v_init_5936_: *mut crate::leanh::LeanObject,
    mut v_as_5937_: *mut crate::leanh::LeanObject,
    mut v_sz_5938_: usize,
    mut v_i_5939_: usize,
    mut v_b_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5946_: u8 = 0;
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5951_: u8 = 0;
    let mut v_a_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5957_: u8 = 0;
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: usize = 0;
    let mut v___x_5970_: usize = 0;
    let mut v_reuseFailAlloc_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v_a_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v_isSharedCheck_5982_: u8 = 0;
    let mut v_unused_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5946_ = lean_usize_dec_lt(v_i_5939_, v_sz_5938_);
                if v___x_5946_ == 0 {
                    v___x_5947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5947_, 0, v_b_5940_);
                    return v___x_5947_;
                } else {
                    v_snd_5948_ = crate::leanh::lean_ctor_get(v_b_5940_, 1);
                    v_isSharedCheck_5982_ = (!crate::leanh::lean_is_exclusive(v_b_5940_)) as u8;
                    if v_isSharedCheck_5982_ == 0 {
                        v_unused_5983_ = crate::leanh::lean_ctor_get(v_b_5940_, 0);
                        crate::leanh::lean_dec(v_unused_5983_);
                        v___x_5950_ = v_b_5940_;
                        v_isShared_5951_ = v_isSharedCheck_5982_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5948_);
                        crate::leanh::lean_dec(v_b_5940_);
                        v___x_5950_ = crate::leanh::lean_box(0);
                        v_isShared_5951_ = v_isSharedCheck_5982_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5952_ = lean_array_uget_borrowed(v_as_5937_, v_i_5939_);
                crate::leanh::lean_inc(v_snd_5948_);
                v___x_5953_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_5936_, v_a_5952_, v_snd_5948_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
                if crate::leanh::lean_obj_tag(v___x_5953_) == 0 {
                    v_a_5954_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_5973_ = (!crate::leanh::lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_5973_ == 0 {
                        v___x_5956_ = v___x_5953_;
                        v_isShared_5957_ = v_isSharedCheck_5973_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5954_);
                        crate::leanh::lean_dec(v___x_5953_);
                        v___x_5956_ = crate::leanh::lean_box(0);
                        v_isShared_5957_ = v_isSharedCheck_5973_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5950_);
                    crate::leanh::lean_dec(v_snd_5948_);
                    v_a_5974_ = crate::leanh::lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_5981_ = (!crate::leanh::lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_5981_ == 0 {
                        v___x_5976_ = v___x_5953_;
                        v_isShared_5977_ = v_isSharedCheck_5981_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5974_);
                        crate::leanh::lean_dec(v___x_5953_);
                        v___x_5976_ = crate::leanh::lean_box(0);
                        v_isShared_5977_ = v_isSharedCheck_5981_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5954_) == 0 {
                    v___x_5958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5958_, 0, v_a_5954_);
                    if v_isShared_5951_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5950_, 0, v___x_5958_);
                        v___x_5960_ = v___x_5950_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5964_, 0, v___x_5958_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5964_, 1, v_snd_5948_);
                        v___x_5960_ = v_reuseFailAlloc_5964_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5956_);
                    crate::leanh::lean_dec(v_snd_5948_);
                    v_a_5965_ = crate::leanh::lean_ctor_get(v_a_5954_, 0);
                    crate::leanh::lean_inc(v_a_5965_);
                    crate::leanh::lean_dec_ref_known(v_a_5954_, 1);
                    v___x_5966_ = crate::leanh::lean_box(0);
                    if v_isShared_5951_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5950_, 1, v_a_5965_);
                        crate::leanh::lean_ctor_set(v___x_5950_, 0, v___x_5966_);
                        v___x_5968_ = v___x_5950_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5966_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 1, v_a_5965_);
                        v___x_5968_ = v_reuseFailAlloc_5972_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5956_, 0, v___x_5960_);
                    v___x_5962_ = v___x_5956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5963_, 0, v___x_5960_);
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
                    v_reuseFailAlloc_5980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
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
    mut v_init_5984_: *mut crate::leanh::LeanObject,
    mut v_as_5985_: *mut crate::leanh::LeanObject,
    mut v_sz_5986_: *mut crate::leanh::LeanObject,
    mut v_i_5987_: *mut crate::leanh::LeanObject,
    mut v_b_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5994_: usize = 0;
    let mut v_i_boxed_5995_: usize = 0;
    let mut v_res_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5994_ = crate::leanh::lean_unbox_usize(v_sz_5986_);
    crate::leanh::lean_dec(v_sz_5986_);
    v_i_boxed_5995_ = crate::leanh::lean_unbox_usize(v_i_5987_);
    crate::leanh::lean_dec(v_i_5987_);
    v_res_5996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_5984_, v_as_5985_, v_sz_boxed_5994_, v_i_boxed_5995_, v_b_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
    crate::leanh::lean_dec(v___y_5992_);
    crate::leanh::lean_dec_ref(v___y_5991_);
    crate::leanh::lean_dec(v___y_5990_);
    crate::leanh::lean_dec_ref(v___y_5989_);
    crate::leanh::lean_dec_ref(v_as_5985_);
    crate::leanh::lean_dec_ref(v_init_5984_);
    return v_res_5996_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(
    mut v_init_5997_: *mut crate::leanh::LeanObject,
    mut v_n_5998_: *mut crate::leanh::LeanObject,
    mut v_b_5999_: *mut crate::leanh::LeanObject,
    mut v___y_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_5997_, v_n_5998_, v_b_5999_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_);
    crate::leanh::lean_dec(v___y_6003_);
    crate::leanh::lean_dec_ref(v___y_6002_);
    crate::leanh::lean_dec(v___y_6001_);
    crate::leanh::lean_dec_ref(v___y_6000_);
    crate::leanh::lean_dec_ref(v_n_5998_);
    crate::leanh::lean_dec_ref(v_init_5997_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(
    mut v_t_6006_: *mut crate::leanh::LeanObject,
    mut v_init_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
    mut v___y_6010_: *mut crate::leanh::LeanObject,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6019_: u8 = 0;
    let mut v_a_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6027_: usize = 0;
    let mut v___x_6028_: usize = 0;
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6033_: u8 = 0;
    let mut v_fst_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6043_: u8 = 0;
    let mut v_a_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6047_: u8 = 0;
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6051_: u8 = 0;
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_a_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6056_: u8 = 0;
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6013_ = crate::leanh::lean_ctor_get(v_t_6006_, 0);
                v_tail_6014_ = crate::leanh::lean_ctor_get(v_t_6006_, 1);
                crate::leanh::lean_inc_ref(v_init_6007_);
                v___x_6015_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_6007_, v_root_6013_, v_init_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
                crate::leanh::lean_dec_ref(v_init_6007_);
                if crate::leanh::lean_obj_tag(v___x_6015_) == 0 {
                    v_a_6016_ = crate::leanh::lean_ctor_get(v___x_6015_, 0);
                    v_isSharedCheck_6052_ = (!crate::leanh::lean_is_exclusive(v___x_6015_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v___x_6018_ = v___x_6015_;
                        v_isShared_6019_ = v_isSharedCheck_6052_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6016_);
                        crate::leanh::lean_dec(v___x_6015_);
                        v___x_6018_ = crate::leanh::lean_box(0);
                        v_isShared_6019_ = v_isSharedCheck_6052_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6053_ = crate::leanh::lean_ctor_get(v___x_6015_, 0);
                    v_isSharedCheck_6060_ = (!crate::leanh::lean_is_exclusive(v___x_6015_)) as u8;
                    if v_isSharedCheck_6060_ == 0 {
                        v___x_6055_ = v___x_6015_;
                        v_isShared_6056_ = v_isSharedCheck_6060_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6053_);
                        crate::leanh::lean_dec(v___x_6015_);
                        v___x_6055_ = crate::leanh::lean_box(0);
                        v_isShared_6056_ = v_isSharedCheck_6060_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6016_) == 0 {
                    v_a_6020_ = crate::leanh::lean_ctor_get(v_a_6016_, 0);
                    crate::leanh::lean_inc(v_a_6020_);
                    crate::leanh::lean_dec_ref_known(v_a_6016_, 1);
                    if v_isShared_6019_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6018_, 0, v_a_6020_);
                        v___x_6022_ = v___x_6018_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_a_6020_);
                        v___x_6022_ = v_reuseFailAlloc_6023_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6018_);
                    v_a_6024_ = crate::leanh::lean_ctor_get(v_a_6016_, 0);
                    crate::leanh::lean_inc(v_a_6024_);
                    crate::leanh::lean_dec_ref_known(v_a_6016_, 1);
                    v___x_6025_ = crate::leanh::lean_box(0);
                    v___x_6026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6026_, 0, v___x_6025_);
                    crate::leanh::lean_ctor_set(v___x_6026_, 1, v_a_6024_);
                    v_sz_6027_ = lean_array_size(v_tail_6014_);
                    v___x_6028_ = 0usize;
                    v___x_6029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_6014_, v_sz_6027_, v___x_6028_, v___x_6026_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
                    if crate::leanh::lean_obj_tag(v___x_6029_) == 0 {
                        v_a_6030_ = crate::leanh::lean_ctor_get(v___x_6029_, 0);
                        v_isSharedCheck_6043_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6029_)) as u8;
                        if v_isSharedCheck_6043_ == 0 {
                            v___x_6032_ = v___x_6029_;
                            v_isShared_6033_ = v_isSharedCheck_6043_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6030_);
                            crate::leanh::lean_dec(v___x_6029_);
                            v___x_6032_ = crate::leanh::lean_box(0);
                            v_isShared_6033_ = v_isSharedCheck_6043_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6044_ = crate::leanh::lean_ctor_get(v___x_6029_, 0);
                        v_isSharedCheck_6051_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6029_)) as u8;
                        if v_isSharedCheck_6051_ == 0 {
                            v___x_6046_ = v___x_6029_;
                            v_isShared_6047_ = v_isSharedCheck_6051_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6044_);
                            crate::leanh::lean_dec(v___x_6029_);
                            v___x_6046_ = crate::leanh::lean_box(0);
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
                v_fst_6034_ = crate::leanh::lean_ctor_get(v_a_6030_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6034_) == 0 {
                    v_snd_6035_ = crate::leanh::lean_ctor_get(v_a_6030_, 1);
                    crate::leanh::lean_inc(v_snd_6035_);
                    crate::leanh::lean_dec(v_a_6030_);
                    if v_isShared_6033_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6032_, 0, v_snd_6035_);
                        v___x_6037_ = v___x_6032_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_snd_6035_);
                        v___x_6037_ = v_reuseFailAlloc_6038_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6034_);
                    crate::leanh::lean_dec(v_a_6030_);
                    v_val_6039_ = crate::leanh::lean_ctor_get(v_fst_6034_, 0);
                    crate::leanh::lean_inc(v_val_6039_);
                    crate::leanh::lean_dec_ref_known(v_fst_6034_, 1);
                    if v_isShared_6033_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6032_, 0, v_val_6039_);
                        v___x_6041_ = v___x_6032_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6042_, 0, v_val_6039_);
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
                    v_reuseFailAlloc_6050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6050_, 0, v_a_6044_);
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
                    v_reuseFailAlloc_6059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_a_6053_);
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
    mut v_t_6061_: *mut crate::leanh::LeanObject,
    mut v_init_6062_: *mut crate::leanh::LeanObject,
    mut v___y_6063_: *mut crate::leanh::LeanObject,
    mut v___y_6064_: *mut crate::leanh::LeanObject,
    mut v___y_6065_: *mut crate::leanh::LeanObject,
    mut v___y_6066_: *mut crate::leanh::LeanObject,
    mut v___y_6067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6068_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(
        v_t_6061_,
        v_init_6062_,
        v___y_6063_,
        v___y_6064_,
        v___y_6065_,
        v___y_6066_,
    );
    crate::leanh::lean_dec(v___y_6066_);
    crate::leanh::lean_dec_ref(v___y_6065_);
    crate::leanh::lean_dec(v___y_6064_);
    crate::leanh::lean_dec_ref(v___y_6063_);
    crate::leanh::lean_dec_ref(v_t_6061_);
    return v_res_6068_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(
    mut v_m_6069_: *mut crate::leanh::LeanObject,
    mut v_a_6070_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: u8 = 0;
    v_buckets_6071_ = crate::leanh::lean_ctor_get(v_m_6069_, 1);
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
    mut v_m_6087_: *mut crate::leanh::LeanObject,
    mut v_a_6088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6089_: u8 = 0;
    let mut v_r_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6089_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_6087_, v_a_6088_);
    crate::leanh::lean_dec(v_a_6088_);
    crate::leanh::lean_dec_ref(v_m_6087_);
    v_r_6090_ = crate::leanh::lean_box((v_res_6089_) as usize);
    return v_r_6090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(
    mut v_a_6091_: *mut crate::leanh::LeanObject,
    mut v_as_6092_: *mut crate::leanh::LeanObject,
    mut v_sz_6093_: usize,
    mut v_i_6094_: usize,
    mut v_b_6095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6097_: u8 = 0;
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6102_: u8 = 0;
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: usize = 0;
    let mut v___x_6109_: usize = 0;
    let mut v_reuseFailAlloc_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: u8 = 0;
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_unused_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6097_ = lean_usize_dec_lt(v_i_6094_, v_sz_6093_);
                if v___x_6097_ == 0 {
                    v___x_6098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6098_, 0, v_b_6095_);
                    return v___x_6098_;
                } else {
                    v_snd_6099_ = crate::leanh::lean_ctor_get(v_b_6095_, 1);
                    v_isSharedCheck_6117_ = (!crate::leanh::lean_is_exclusive(v_b_6095_)) as u8;
                    if v_isSharedCheck_6117_ == 0 {
                        v_unused_6118_ = crate::leanh::lean_ctor_get(v_b_6095_, 0);
                        crate::leanh::lean_dec(v_unused_6118_);
                        v___x_6101_ = v_b_6095_;
                        v_isShared_6102_ = v_isSharedCheck_6117_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6099_);
                        crate::leanh::lean_dec(v_b_6095_);
                        v___x_6101_ = crate::leanh::lean_box(0);
                        v_isShared_6102_ = v_isSharedCheck_6117_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6103_ = crate::leanh::lean_box(0);
                v_a_6112_ = lean_array_uget_borrowed(v_as_6092_, v_i_6094_);
                if crate::leanh::lean_obj_tag(v_a_6112_) == 0 {
                    v_a_6105_ = v_snd_6099_;
                    state = 2;
                    continue;
                } else {
                    v_val_6113_ = crate::leanh::lean_ctor_get(v_a_6112_, 0);
                    v___x_6114_ = l_Lean_LocalDecl_fvarId(v_val_6113_);
                    v___x_6115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6091_, v___x_6114_);
                    if v___x_6115_ == 0 {
                        crate::leanh::lean_dec(v___x_6114_);
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
                    crate::leanh::lean_ctor_set(v___x_6101_, 1, v_a_6105_);
                    crate::leanh::lean_ctor_set(v___x_6101_, 0, v___x_6103_);
                    v___x_6107_ = v___x_6101_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6111_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6111_, 0, v___x_6103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6111_, 1, v_a_6105_);
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
    mut v_a_6119_: *mut crate::leanh::LeanObject,
    mut v_as_6120_: *mut crate::leanh::LeanObject,
    mut v_sz_6121_: *mut crate::leanh::LeanObject,
    mut v_i_6122_: *mut crate::leanh::LeanObject,
    mut v_b_6123_: *mut crate::leanh::LeanObject,
    mut v___y_6124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6125_: usize = 0;
    let mut v_i_boxed_6126_: usize = 0;
    let mut v_res_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6125_ = crate::leanh::lean_unbox_usize(v_sz_6121_);
    crate::leanh::lean_dec(v_sz_6121_);
    v_i_boxed_6126_ = crate::leanh::lean_unbox_usize(v_i_6122_);
    crate::leanh::lean_dec(v_i_6122_);
    v_res_6127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_6119_, v_as_6120_, v_sz_boxed_6125_, v_i_boxed_6126_, v_b_6123_);
    crate::leanh::lean_dec_ref(v_as_6120_);
    crate::leanh::lean_dec_ref(v_a_6119_);
    return v_res_6127_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(
    mut v_a_6128_: *mut crate::leanh::LeanObject,
    mut v_as_6129_: *mut crate::leanh::LeanObject,
    mut v_sz_6130_: usize,
    mut v_i_6131_: usize,
    mut v_b_6132_: *mut crate::leanh::LeanObject,
    mut v___y_6133_: *mut crate::leanh::LeanObject,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
    mut v___y_6136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6138_: u8 = 0;
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: usize = 0;
    let mut v___x_6150_: usize = 0;
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6158_: u8 = 0;
    let mut v_unused_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6138_ = lean_usize_dec_lt(v_i_6131_, v_sz_6130_);
                if v___x_6138_ == 0 {
                    v___x_6139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6139_, 0, v_b_6132_);
                    return v___x_6139_;
                } else {
                    v_snd_6140_ = crate::leanh::lean_ctor_get(v_b_6132_, 1);
                    v_isSharedCheck_6158_ = (!crate::leanh::lean_is_exclusive(v_b_6132_)) as u8;
                    if v_isSharedCheck_6158_ == 0 {
                        v_unused_6159_ = crate::leanh::lean_ctor_get(v_b_6132_, 0);
                        crate::leanh::lean_dec(v_unused_6159_);
                        v___x_6142_ = v_b_6132_;
                        v_isShared_6143_ = v_isSharedCheck_6158_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6140_);
                        crate::leanh::lean_dec(v_b_6132_);
                        v___x_6142_ = crate::leanh::lean_box(0);
                        v_isShared_6143_ = v_isSharedCheck_6158_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6144_ = crate::leanh::lean_box(0);
                v_a_6153_ = lean_array_uget_borrowed(v_as_6129_, v_i_6131_);
                if crate::leanh::lean_obj_tag(v_a_6153_) == 0 {
                    v_a_6146_ = v_snd_6140_;
                    state = 2;
                    continue;
                } else {
                    v_val_6154_ = crate::leanh::lean_ctor_get(v_a_6153_, 0);
                    v___x_6155_ = l_Lean_LocalDecl_fvarId(v_val_6154_);
                    v___x_6156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6128_, v___x_6155_);
                    if v___x_6156_ == 0 {
                        crate::leanh::lean_dec(v___x_6155_);
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
                    crate::leanh::lean_ctor_set(v___x_6142_, 1, v_a_6146_);
                    crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6144_);
                    v___x_6148_ = v___x_6142_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6152_, 0, v___x_6144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6152_, 1, v_a_6146_);
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
    mut v_a_6160_: *mut crate::leanh::LeanObject,
    mut v_as_6161_: *mut crate::leanh::LeanObject,
    mut v_sz_6162_: *mut crate::leanh::LeanObject,
    mut v_i_6163_: *mut crate::leanh::LeanObject,
    mut v_b_6164_: *mut crate::leanh::LeanObject,
    mut v___y_6165_: *mut crate::leanh::LeanObject,
    mut v___y_6166_: *mut crate::leanh::LeanObject,
    mut v___y_6167_: *mut crate::leanh::LeanObject,
    mut v___y_6168_: *mut crate::leanh::LeanObject,
    mut v___y_6169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6170_: usize = 0;
    let mut v_i_boxed_6171_: usize = 0;
    let mut v_res_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6170_ = crate::leanh::lean_unbox_usize(v_sz_6162_);
    crate::leanh::lean_dec(v_sz_6162_);
    v_i_boxed_6171_ = crate::leanh::lean_unbox_usize(v_i_6163_);
    crate::leanh::lean_dec(v_i_6163_);
    v_res_6172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_6160_, v_as_6161_, v_sz_boxed_6170_, v_i_boxed_6171_, v_b_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
    crate::leanh::lean_dec(v___y_6168_);
    crate::leanh::lean_dec_ref(v___y_6167_);
    crate::leanh::lean_dec(v___y_6166_);
    crate::leanh::lean_dec_ref(v___y_6165_);
    crate::leanh::lean_dec_ref(v_as_6161_);
    crate::leanh::lean_dec_ref(v_a_6160_);
    return v_res_6172_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(
    mut v_init_6173_: *mut crate::leanh::LeanObject,
    mut v_a_6174_: *mut crate::leanh::LeanObject,
    mut v_n_6175_: *mut crate::leanh::LeanObject,
    mut v_b_6176_: *mut crate::leanh::LeanObject,
    mut v___y_6177_: *mut crate::leanh::LeanObject,
    mut v___y_6178_: *mut crate::leanh::LeanObject,
    mut v___y_6179_: *mut crate::leanh::LeanObject,
    mut v___y_6180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6185_: usize = 0;
    let mut v___x_6186_: usize = 0;
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6191_: u8 = 0;
    let mut v_fst_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6202_: u8 = 0;
    let mut v_a_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6206_: u8 = 0;
    let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_vs_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6214_: usize = 0;
    let mut v___x_6215_: usize = 0;
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6220_: u8 = 0;
    let mut v_fst_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_a_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_6175_) == 0 {
                    v_cs_6182_ = crate::leanh::lean_ctor_get(v_n_6175_, 0);
                    v___x_6183_ = crate::leanh::lean_box(0);
                    v___x_6184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6184_, 0, v___x_6183_);
                    crate::leanh::lean_ctor_set(v___x_6184_, 1, v_b_6176_);
                    v_sz_6185_ = lean_array_size(v_cs_6182_);
                    v___x_6186_ = 0usize;
                    v___x_6187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_6173_, v_a_6174_, v_cs_6182_, v_sz_6185_, v___x_6186_, v___x_6184_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
                    if crate::leanh::lean_obj_tag(v___x_6187_) == 0 {
                        v_a_6188_ = crate::leanh::lean_ctor_get(v___x_6187_, 0);
                        v_isSharedCheck_6202_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6187_)) as u8;
                        if v_isSharedCheck_6202_ == 0 {
                            v___x_6190_ = v___x_6187_;
                            v_isShared_6191_ = v_isSharedCheck_6202_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6188_);
                            crate::leanh::lean_dec(v___x_6187_);
                            v___x_6190_ = crate::leanh::lean_box(0);
                            v_isShared_6191_ = v_isSharedCheck_6202_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6203_ = crate::leanh::lean_ctor_get(v___x_6187_, 0);
                        v_isSharedCheck_6210_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6187_)) as u8;
                        if v_isSharedCheck_6210_ == 0 {
                            v___x_6205_ = v___x_6187_;
                            v_isShared_6206_ = v_isSharedCheck_6210_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6203_);
                            crate::leanh::lean_dec(v___x_6187_);
                            v___x_6205_ = crate::leanh::lean_box(0);
                            v_isShared_6206_ = v_isSharedCheck_6210_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6211_ = crate::leanh::lean_ctor_get(v_n_6175_, 0);
                    v___x_6212_ = crate::leanh::lean_box(0);
                    v___x_6213_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6213_, 0, v___x_6212_);
                    crate::leanh::lean_ctor_set(v___x_6213_, 1, v_b_6176_);
                    v_sz_6214_ = lean_array_size(v_vs_6211_);
                    v___x_6215_ = 0usize;
                    v___x_6216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_6174_, v_vs_6211_, v_sz_6214_, v___x_6215_, v___x_6213_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
                    if crate::leanh::lean_obj_tag(v___x_6216_) == 0 {
                        v_a_6217_ = crate::leanh::lean_ctor_get(v___x_6216_, 0);
                        v_isSharedCheck_6231_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6216_)) as u8;
                        if v_isSharedCheck_6231_ == 0 {
                            v___x_6219_ = v___x_6216_;
                            v_isShared_6220_ = v_isSharedCheck_6231_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6217_);
                            crate::leanh::lean_dec(v___x_6216_);
                            v___x_6219_ = crate::leanh::lean_box(0);
                            v_isShared_6220_ = v_isSharedCheck_6231_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6232_ = crate::leanh::lean_ctor_get(v___x_6216_, 0);
                        v_isSharedCheck_6239_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6216_)) as u8;
                        if v_isSharedCheck_6239_ == 0 {
                            v___x_6234_ = v___x_6216_;
                            v_isShared_6235_ = v_isSharedCheck_6239_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6232_);
                            crate::leanh::lean_dec(v___x_6216_);
                            v___x_6234_ = crate::leanh::lean_box(0);
                            v_isShared_6235_ = v_isSharedCheck_6239_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6192_ = crate::leanh::lean_ctor_get(v_a_6188_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6192_) == 0 {
                    v_snd_6193_ = crate::leanh::lean_ctor_get(v_a_6188_, 1);
                    crate::leanh::lean_inc(v_snd_6193_);
                    crate::leanh::lean_dec(v_a_6188_);
                    v___x_6194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6194_, 0, v_snd_6193_);
                    if v_isShared_6191_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6190_, 0, v___x_6194_);
                        v___x_6196_ = v___x_6190_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6197_, 0, v___x_6194_);
                        v___x_6196_ = v_reuseFailAlloc_6197_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6192_);
                    crate::leanh::lean_dec(v_a_6188_);
                    v_val_6198_ = crate::leanh::lean_ctor_get(v_fst_6192_, 0);
                    crate::leanh::lean_inc(v_val_6198_);
                    crate::leanh::lean_dec_ref_known(v_fst_6192_, 1);
                    if v_isShared_6191_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6190_, 0, v_val_6198_);
                        v___x_6200_ = v___x_6190_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 0, v_val_6198_);
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
                    v_reuseFailAlloc_6209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
                    v___x_6208_ = v_reuseFailAlloc_6209_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6208_;
            }
            6 => {
                v_fst_6221_ = crate::leanh::lean_ctor_get(v_a_6217_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6221_) == 0 {
                    v_snd_6222_ = crate::leanh::lean_ctor_get(v_a_6217_, 1);
                    crate::leanh::lean_inc(v_snd_6222_);
                    crate::leanh::lean_dec(v_a_6217_);
                    v___x_6223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6223_, 0, v_snd_6222_);
                    if v_isShared_6220_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6219_, 0, v___x_6223_);
                        v___x_6225_ = v___x_6219_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6226_, 0, v___x_6223_);
                        v___x_6225_ = v_reuseFailAlloc_6226_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6221_);
                    crate::leanh::lean_dec(v_a_6217_);
                    v_val_6227_ = crate::leanh::lean_ctor_get(v_fst_6221_, 0);
                    crate::leanh::lean_inc(v_val_6227_);
                    crate::leanh::lean_dec_ref_known(v_fst_6221_, 1);
                    if v_isShared_6220_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6219_, 0, v_val_6227_);
                        v___x_6229_ = v___x_6219_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_val_6227_);
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
                    v_reuseFailAlloc_6238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
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
    mut v_init_6240_: *mut crate::leanh::LeanObject,
    mut v_a_6241_: *mut crate::leanh::LeanObject,
    mut v_as_6242_: *mut crate::leanh::LeanObject,
    mut v_sz_6243_: usize,
    mut v_i_6244_: usize,
    mut v_b_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
    mut v___y_6248_: *mut crate::leanh::LeanObject,
    mut v___y_6249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6251_: u8 = 0;
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6256_: u8 = 0;
    let mut v_a_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6262_: u8 = 0;
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: usize = 0;
    let mut v___x_6275_: usize = 0;
    let mut v_reuseFailAlloc_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6278_: u8 = 0;
    let mut v_a_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6282_: u8 = 0;
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut v_isSharedCheck_6287_: u8 = 0;
    let mut v_unused_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6251_ = lean_usize_dec_lt(v_i_6244_, v_sz_6243_);
                if v___x_6251_ == 0 {
                    v___x_6252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6252_, 0, v_b_6245_);
                    return v___x_6252_;
                } else {
                    v_snd_6253_ = crate::leanh::lean_ctor_get(v_b_6245_, 1);
                    v_isSharedCheck_6287_ = (!crate::leanh::lean_is_exclusive(v_b_6245_)) as u8;
                    if v_isSharedCheck_6287_ == 0 {
                        v_unused_6288_ = crate::leanh::lean_ctor_get(v_b_6245_, 0);
                        crate::leanh::lean_dec(v_unused_6288_);
                        v___x_6255_ = v_b_6245_;
                        v_isShared_6256_ = v_isSharedCheck_6287_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6253_);
                        crate::leanh::lean_dec(v_b_6245_);
                        v___x_6255_ = crate::leanh::lean_box(0);
                        v_isShared_6256_ = v_isSharedCheck_6287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6257_ = lean_array_uget_borrowed(v_as_6242_, v_i_6244_);
                crate::leanh::lean_inc(v_snd_6253_);
                v___x_6258_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_6240_, v_a_6241_, v_a_6257_, v_snd_6253_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_);
                if crate::leanh::lean_obj_tag(v___x_6258_) == 0 {
                    v_a_6259_ = crate::leanh::lean_ctor_get(v___x_6258_, 0);
                    v_isSharedCheck_6278_ = (!crate::leanh::lean_is_exclusive(v___x_6258_)) as u8;
                    if v_isSharedCheck_6278_ == 0 {
                        v___x_6261_ = v___x_6258_;
                        v_isShared_6262_ = v_isSharedCheck_6278_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6259_);
                        crate::leanh::lean_dec(v___x_6258_);
                        v___x_6261_ = crate::leanh::lean_box(0);
                        v_isShared_6262_ = v_isSharedCheck_6278_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6255_);
                    crate::leanh::lean_dec(v_snd_6253_);
                    v_a_6279_ = crate::leanh::lean_ctor_get(v___x_6258_, 0);
                    v_isSharedCheck_6286_ = (!crate::leanh::lean_is_exclusive(v___x_6258_)) as u8;
                    if v_isSharedCheck_6286_ == 0 {
                        v___x_6281_ = v___x_6258_;
                        v_isShared_6282_ = v_isSharedCheck_6286_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6279_);
                        crate::leanh::lean_dec(v___x_6258_);
                        v___x_6281_ = crate::leanh::lean_box(0);
                        v_isShared_6282_ = v_isSharedCheck_6286_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6259_) == 0 {
                    v___x_6263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6263_, 0, v_a_6259_);
                    if v_isShared_6256_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6255_, 0, v___x_6263_);
                        v___x_6265_ = v___x_6255_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6269_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6269_, 0, v___x_6263_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6269_, 1, v_snd_6253_);
                        v___x_6265_ = v_reuseFailAlloc_6269_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6261_);
                    crate::leanh::lean_dec(v_snd_6253_);
                    v_a_6270_ = crate::leanh::lean_ctor_get(v_a_6259_, 0);
                    crate::leanh::lean_inc(v_a_6270_);
                    crate::leanh::lean_dec_ref_known(v_a_6259_, 1);
                    v___x_6271_ = crate::leanh::lean_box(0);
                    if v_isShared_6256_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6255_, 1, v_a_6270_);
                        crate::leanh::lean_ctor_set(v___x_6255_, 0, v___x_6271_);
                        v___x_6273_ = v___x_6255_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6277_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6277_, 0, v___x_6271_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6277_, 1, v_a_6270_);
                        v___x_6273_ = v_reuseFailAlloc_6277_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6261_, 0, v___x_6265_);
                    v___x_6267_ = v___x_6261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v___x_6265_);
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
                    v_reuseFailAlloc_6285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_a_6279_);
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
    mut v_init_6289_: *mut crate::leanh::LeanObject,
    mut v_a_6290_: *mut crate::leanh::LeanObject,
    mut v_as_6291_: *mut crate::leanh::LeanObject,
    mut v_sz_6292_: *mut crate::leanh::LeanObject,
    mut v_i_6293_: *mut crate::leanh::LeanObject,
    mut v_b_6294_: *mut crate::leanh::LeanObject,
    mut v___y_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
    mut v___y_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6300_: usize = 0;
    let mut v_i_boxed_6301_: usize = 0;
    let mut v_res_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6300_ = crate::leanh::lean_unbox_usize(v_sz_6292_);
    crate::leanh::lean_dec(v_sz_6292_);
    v_i_boxed_6301_ = crate::leanh::lean_unbox_usize(v_i_6293_);
    crate::leanh::lean_dec(v_i_6293_);
    v_res_6302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_6289_, v_a_6290_, v_as_6291_, v_sz_boxed_6300_, v_i_boxed_6301_, v_b_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_);
    crate::leanh::lean_dec(v___y_6298_);
    crate::leanh::lean_dec_ref(v___y_6297_);
    crate::leanh::lean_dec(v___y_6296_);
    crate::leanh::lean_dec_ref(v___y_6295_);
    crate::leanh::lean_dec_ref(v_as_6291_);
    crate::leanh::lean_dec_ref(v_a_6290_);
    crate::leanh::lean_dec_ref(v_init_6289_);
    return v_res_6302_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(
    mut v_init_6303_: *mut crate::leanh::LeanObject,
    mut v_a_6304_: *mut crate::leanh::LeanObject,
    mut v_n_6305_: *mut crate::leanh::LeanObject,
    mut v_b_6306_: *mut crate::leanh::LeanObject,
    mut v___y_6307_: *mut crate::leanh::LeanObject,
    mut v___y_6308_: *mut crate::leanh::LeanObject,
    mut v___y_6309_: *mut crate::leanh::LeanObject,
    mut v___y_6310_: *mut crate::leanh::LeanObject,
    mut v___y_6311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6312_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_6303_, v_a_6304_, v_n_6305_, v_b_6306_, v___y_6307_, v___y_6308_, v___y_6309_, v___y_6310_);
    crate::leanh::lean_dec(v___y_6310_);
    crate::leanh::lean_dec_ref(v___y_6309_);
    crate::leanh::lean_dec(v___y_6308_);
    crate::leanh::lean_dec_ref(v___y_6307_);
    crate::leanh::lean_dec_ref(v_n_6305_);
    crate::leanh::lean_dec_ref(v_a_6304_);
    crate::leanh::lean_dec_ref(v_init_6303_);
    return v_res_6312_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(
    mut v_a_6313_: *mut crate::leanh::LeanObject,
    mut v_as_6314_: *mut crate::leanh::LeanObject,
    mut v_sz_6315_: usize,
    mut v_i_6316_: usize,
    mut v_b_6317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6319_: u8 = 0;
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6324_: u8 = 0;
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: usize = 0;
    let mut v___x_6331_: usize = 0;
    let mut v_reuseFailAlloc_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: u8 = 0;
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6339_: u8 = 0;
    let mut v_unused_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6319_ = lean_usize_dec_lt(v_i_6316_, v_sz_6315_);
                if v___x_6319_ == 0 {
                    v___x_6320_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6320_, 0, v_b_6317_);
                    return v___x_6320_;
                } else {
                    v_snd_6321_ = crate::leanh::lean_ctor_get(v_b_6317_, 1);
                    v_isSharedCheck_6339_ = (!crate::leanh::lean_is_exclusive(v_b_6317_)) as u8;
                    if v_isSharedCheck_6339_ == 0 {
                        v_unused_6340_ = crate::leanh::lean_ctor_get(v_b_6317_, 0);
                        crate::leanh::lean_dec(v_unused_6340_);
                        v___x_6323_ = v_b_6317_;
                        v_isShared_6324_ = v_isSharedCheck_6339_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6321_);
                        crate::leanh::lean_dec(v_b_6317_);
                        v___x_6323_ = crate::leanh::lean_box(0);
                        v_isShared_6324_ = v_isSharedCheck_6339_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6325_ = crate::leanh::lean_box(0);
                v_a_6334_ = lean_array_uget_borrowed(v_as_6314_, v_i_6316_);
                if crate::leanh::lean_obj_tag(v_a_6334_) == 0 {
                    v_a_6327_ = v_snd_6321_;
                    state = 2;
                    continue;
                } else {
                    v_val_6335_ = crate::leanh::lean_ctor_get(v_a_6334_, 0);
                    v___x_6336_ = l_Lean_LocalDecl_fvarId(v_val_6335_);
                    v___x_6337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6313_, v___x_6336_);
                    if v___x_6337_ == 0 {
                        crate::leanh::lean_dec(v___x_6336_);
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
                    crate::leanh::lean_ctor_set(v___x_6323_, 1, v_a_6327_);
                    crate::leanh::lean_ctor_set(v___x_6323_, 0, v___x_6325_);
                    v___x_6329_ = v___x_6323_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6333_, 0, v___x_6325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6333_, 1, v_a_6327_);
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
    mut v_a_6341_: *mut crate::leanh::LeanObject,
    mut v_as_6342_: *mut crate::leanh::LeanObject,
    mut v_sz_6343_: *mut crate::leanh::LeanObject,
    mut v_i_6344_: *mut crate::leanh::LeanObject,
    mut v_b_6345_: *mut crate::leanh::LeanObject,
    mut v___y_6346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6347_: usize = 0;
    let mut v_i_boxed_6348_: usize = 0;
    let mut v_res_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6347_ = crate::leanh::lean_unbox_usize(v_sz_6343_);
    crate::leanh::lean_dec(v_sz_6343_);
    v_i_boxed_6348_ = crate::leanh::lean_unbox_usize(v_i_6344_);
    crate::leanh::lean_dec(v_i_6344_);
    v_res_6349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_6341_, v_as_6342_, v_sz_boxed_6347_, v_i_boxed_6348_, v_b_6345_);
    crate::leanh::lean_dec_ref(v_as_6342_);
    crate::leanh::lean_dec_ref(v_a_6341_);
    return v_res_6349_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(
    mut v_a_6350_: *mut crate::leanh::LeanObject,
    mut v_as_6351_: *mut crate::leanh::LeanObject,
    mut v_sz_6352_: usize,
    mut v_i_6353_: usize,
    mut v_b_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
    mut v___y_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6360_: u8 = 0;
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: usize = 0;
    let mut v___x_6372_: usize = 0;
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: u8 = 0;
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6380_: u8 = 0;
    let mut v_unused_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6360_ = lean_usize_dec_lt(v_i_6353_, v_sz_6352_);
                if v___x_6360_ == 0 {
                    v___x_6361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6361_, 0, v_b_6354_);
                    return v___x_6361_;
                } else {
                    v_snd_6362_ = crate::leanh::lean_ctor_get(v_b_6354_, 1);
                    v_isSharedCheck_6380_ = (!crate::leanh::lean_is_exclusive(v_b_6354_)) as u8;
                    if v_isSharedCheck_6380_ == 0 {
                        v_unused_6381_ = crate::leanh::lean_ctor_get(v_b_6354_, 0);
                        crate::leanh::lean_dec(v_unused_6381_);
                        v___x_6364_ = v_b_6354_;
                        v_isShared_6365_ = v_isSharedCheck_6380_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6362_);
                        crate::leanh::lean_dec(v_b_6354_);
                        v___x_6364_ = crate::leanh::lean_box(0);
                        v_isShared_6365_ = v_isSharedCheck_6380_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6366_ = crate::leanh::lean_box(0);
                v_a_6375_ = lean_array_uget_borrowed(v_as_6351_, v_i_6353_);
                if crate::leanh::lean_obj_tag(v_a_6375_) == 0 {
                    v_a_6368_ = v_snd_6362_;
                    state = 2;
                    continue;
                } else {
                    v_val_6376_ = crate::leanh::lean_ctor_get(v_a_6375_, 0);
                    v___x_6377_ = l_Lean_LocalDecl_fvarId(v_val_6376_);
                    v___x_6378_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6350_, v___x_6377_);
                    if v___x_6378_ == 0 {
                        crate::leanh::lean_dec(v___x_6377_);
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
                    crate::leanh::lean_ctor_set(v___x_6364_, 1, v_a_6368_);
                    crate::leanh::lean_ctor_set(v___x_6364_, 0, v___x_6366_);
                    v___x_6370_ = v___x_6364_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6374_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6374_, 0, v___x_6366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6374_, 1, v_a_6368_);
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
    mut v_a_6382_: *mut crate::leanh::LeanObject,
    mut v_as_6383_: *mut crate::leanh::LeanObject,
    mut v_sz_6384_: *mut crate::leanh::LeanObject,
    mut v_i_6385_: *mut crate::leanh::LeanObject,
    mut v_b_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
    mut v___y_6391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6392_: usize = 0;
    let mut v_i_boxed_6393_: usize = 0;
    let mut v_res_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6392_ = crate::leanh::lean_unbox_usize(v_sz_6384_);
    crate::leanh::lean_dec(v_sz_6384_);
    v_i_boxed_6393_ = crate::leanh::lean_unbox_usize(v_i_6385_);
    crate::leanh::lean_dec(v_i_6385_);
    v_res_6394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_6382_, v_as_6383_, v_sz_boxed_6392_, v_i_boxed_6393_, v_b_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
    crate::leanh::lean_dec(v___y_6390_);
    crate::leanh::lean_dec_ref(v___y_6389_);
    crate::leanh::lean_dec(v___y_6388_);
    crate::leanh::lean_dec_ref(v___y_6387_);
    crate::leanh::lean_dec_ref(v_as_6383_);
    crate::leanh::lean_dec_ref(v_a_6382_);
    return v_res_6394_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(
    mut v_a_6395_: *mut crate::leanh::LeanObject,
    mut v_t_6396_: *mut crate::leanh::LeanObject,
    mut v_init_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6409_: u8 = 0;
    let mut v_a_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6417_: usize = 0;
    let mut v___x_6418_: usize = 0;
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6423_: u8 = 0;
    let mut v_fst_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6433_: u8 = 0;
    let mut v_a_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6437_: u8 = 0;
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6441_: u8 = 0;
    let mut v_isSharedCheck_6442_: u8 = 0;
    let mut v_a_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6446_: u8 = 0;
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6403_ = crate::leanh::lean_ctor_get(v_t_6396_, 0);
                v_tail_6404_ = crate::leanh::lean_ctor_get(v_t_6396_, 1);
                crate::leanh::lean_inc_ref(v_init_6397_);
                v___x_6405_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_6397_, v_a_6395_, v_root_6403_, v_init_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_);
                crate::leanh::lean_dec_ref(v_init_6397_);
                if crate::leanh::lean_obj_tag(v___x_6405_) == 0 {
                    v_a_6406_ = crate::leanh::lean_ctor_get(v___x_6405_, 0);
                    v_isSharedCheck_6442_ = (!crate::leanh::lean_is_exclusive(v___x_6405_)) as u8;
                    if v_isSharedCheck_6442_ == 0 {
                        v___x_6408_ = v___x_6405_;
                        v_isShared_6409_ = v_isSharedCheck_6442_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6406_);
                        crate::leanh::lean_dec(v___x_6405_);
                        v___x_6408_ = crate::leanh::lean_box(0);
                        v_isShared_6409_ = v_isSharedCheck_6442_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6443_ = crate::leanh::lean_ctor_get(v___x_6405_, 0);
                    v_isSharedCheck_6450_ = (!crate::leanh::lean_is_exclusive(v___x_6405_)) as u8;
                    if v_isSharedCheck_6450_ == 0 {
                        v___x_6445_ = v___x_6405_;
                        v_isShared_6446_ = v_isSharedCheck_6450_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6443_);
                        crate::leanh::lean_dec(v___x_6405_);
                        v___x_6445_ = crate::leanh::lean_box(0);
                        v_isShared_6446_ = v_isSharedCheck_6450_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6406_) == 0 {
                    v_a_6410_ = crate::leanh::lean_ctor_get(v_a_6406_, 0);
                    crate::leanh::lean_inc(v_a_6410_);
                    crate::leanh::lean_dec_ref_known(v_a_6406_, 1);
                    if v_isShared_6409_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6408_, 0, v_a_6410_);
                        v___x_6412_ = v___x_6408_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6413_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_a_6410_);
                        v___x_6412_ = v_reuseFailAlloc_6413_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6408_);
                    v_a_6414_ = crate::leanh::lean_ctor_get(v_a_6406_, 0);
                    crate::leanh::lean_inc(v_a_6414_);
                    crate::leanh::lean_dec_ref_known(v_a_6406_, 1);
                    v___x_6415_ = crate::leanh::lean_box(0);
                    v___x_6416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6416_, 0, v___x_6415_);
                    crate::leanh::lean_ctor_set(v___x_6416_, 1, v_a_6414_);
                    v_sz_6417_ = lean_array_size(v_tail_6404_);
                    v___x_6418_ = 0usize;
                    v___x_6419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_6395_, v_tail_6404_, v_sz_6417_, v___x_6418_, v___x_6416_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_);
                    if crate::leanh::lean_obj_tag(v___x_6419_) == 0 {
                        v_a_6420_ = crate::leanh::lean_ctor_get(v___x_6419_, 0);
                        v_isSharedCheck_6433_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6419_)) as u8;
                        if v_isSharedCheck_6433_ == 0 {
                            v___x_6422_ = v___x_6419_;
                            v_isShared_6423_ = v_isSharedCheck_6433_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6420_);
                            crate::leanh::lean_dec(v___x_6419_);
                            v___x_6422_ = crate::leanh::lean_box(0);
                            v_isShared_6423_ = v_isSharedCheck_6433_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6434_ = crate::leanh::lean_ctor_get(v___x_6419_, 0);
                        v_isSharedCheck_6441_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6419_)) as u8;
                        if v_isSharedCheck_6441_ == 0 {
                            v___x_6436_ = v___x_6419_;
                            v_isShared_6437_ = v_isSharedCheck_6441_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6434_);
                            crate::leanh::lean_dec(v___x_6419_);
                            v___x_6436_ = crate::leanh::lean_box(0);
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
                v_fst_6424_ = crate::leanh::lean_ctor_get(v_a_6420_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6424_) == 0 {
                    v_snd_6425_ = crate::leanh::lean_ctor_get(v_a_6420_, 1);
                    crate::leanh::lean_inc(v_snd_6425_);
                    crate::leanh::lean_dec(v_a_6420_);
                    if v_isShared_6423_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6422_, 0, v_snd_6425_);
                        v___x_6427_ = v___x_6422_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6428_, 0, v_snd_6425_);
                        v___x_6427_ = v_reuseFailAlloc_6428_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6424_);
                    crate::leanh::lean_dec(v_a_6420_);
                    v_val_6429_ = crate::leanh::lean_ctor_get(v_fst_6424_, 0);
                    crate::leanh::lean_inc(v_val_6429_);
                    crate::leanh::lean_dec_ref_known(v_fst_6424_, 1);
                    if v_isShared_6423_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6422_, 0, v_val_6429_);
                        v___x_6431_ = v___x_6422_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6432_, 0, v_val_6429_);
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
                    v_reuseFailAlloc_6440_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6440_, 0, v_a_6434_);
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
                    v_reuseFailAlloc_6449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_a_6443_);
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
    mut v_a_6451_: *mut crate::leanh::LeanObject,
    mut v_t_6452_: *mut crate::leanh::LeanObject,
    mut v_init_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
    mut v___y_6455_: *mut crate::leanh::LeanObject,
    mut v___y_6456_: *mut crate::leanh::LeanObject,
    mut v___y_6457_: *mut crate::leanh::LeanObject,
    mut v___y_6458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6459_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(
        v_a_6451_,
        v_t_6452_,
        v_init_6453_,
        v___y_6454_,
        v___y_6455_,
        v___y_6456_,
        v___y_6457_,
    );
    crate::leanh::lean_dec(v___y_6457_);
    crate::leanh::lean_dec_ref(v___y_6456_);
    crate::leanh::lean_dec(v___y_6455_);
    crate::leanh::lean_dec_ref(v___y_6454_);
    crate::leanh::lean_dec_ref(v_t_6452_);
    crate::leanh::lean_dec_ref(v_a_6451_);
    return v_res_6459_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__2(
    mut v_candidates_6462_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6463_: *mut crate::leanh::LeanObject,
    mut v___f_6464_: *mut crate::leanh::LeanObject,
    mut v___f_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
    mut v___y_6468_: *mut crate::leanh::LeanObject,
    mut v___y_6469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: u8 = 0;
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6496_: u8 = 0;
    let mut v_a_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6504_: u8 = 0;
    let mut v___x_6505_: u8 = 0;
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: u8 = 0;
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6516_: u8 = 0;
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6520_: u8 = 0;
    let mut v_a_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6524_: u8 = 0;
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_a_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_6471_ = crate::leanh::lean_ctor_get(v___y_6466_, 2);
                v_decls_6472_ = crate::leanh::lean_ctor_get(v_lctx_6471_, 1);
                crate::leanh::lean_inc_ref(v_decls_6472_);
                v___x_6473_ =
                    l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(
                        v_decls_6472_,
                        v_candidates_6462_,
                        v___y_6466_,
                        v___y_6467_,
                        v___y_6468_,
                        v___y_6469_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6473_) == 0 {
                    v_a_6474_ = crate::leanh::lean_ctor_get(v___x_6473_, 0);
                    crate::leanh::lean_inc(v_a_6474_);
                    crate::leanh::lean_dec_ref_known(v___x_6473_, 1);
                    v___x_6475_ = l_Lean_MVarId_getType(
                        v_mvarId_6463_,
                        v___y_6466_,
                        v___y_6467_,
                        v___y_6468_,
                        v___y_6469_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6475_) == 0 {
                        v_a_6476_ = crate::leanh::lean_ctor_get(v___x_6475_, 0);
                        crate::leanh::lean_inc(v_a_6476_);
                        crate::leanh::lean_dec_ref_known(v___x_6475_, 1);
                        v___x_6477_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_6476_, v___y_6467_);
                        v_a_6478_ = crate::leanh::lean_ctor_get(v___x_6477_, 0);
                        crate::leanh::lean_inc(v_a_6478_);
                        crate::leanh::lean_dec_ref(v___x_6477_);
                        v___x_6479_ = lean_st_mk_ref(v_a_6474_);
                        v___x_6505_ = l_Lean_Expr_hasFVar(v_a_6478_);
                        if v___x_6505_ == 0 {
                            crate::leanh::lean_dec(v_a_6478_);
                            crate::leanh::lean_dec_ref(v___f_6465_);
                            v___x_6506_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_6469_);
                            crate::leanh::lean_inc_ref(v___y_6468_);
                            crate::leanh::lean_inc(v___y_6467_);
                            crate::leanh::lean_inc_ref(v___y_6466_);
                            crate::leanh::lean_inc(v___x_6479_);
                            v___x_6507_ = crate::leanh::lean_apply_7(
                                v___f_6464_,
                                v___x_6506_,
                                v___x_6479_,
                                v___y_6466_,
                                v___y_6467_,
                                v___y_6468_,
                                v___y_6469_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_6481_ = v___x_6507_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0;
                            v___x_6509_ = 0;
                            v___x_6510_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_6508_, v___f_6465_, v_a_6478_, v___x_6509_, v___x_6479_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
                            if crate::leanh::lean_obj_tag(v___x_6510_) == 0 {
                                v_a_6511_ = crate::leanh::lean_ctor_get(v___x_6510_, 0);
                                crate::leanh::lean_inc(v_a_6511_);
                                crate::leanh::lean_dec_ref_known(v___x_6510_, 1);
                                crate::leanh::lean_inc(v___y_6469_);
                                crate::leanh::lean_inc_ref(v___y_6468_);
                                crate::leanh::lean_inc(v___y_6467_);
                                crate::leanh::lean_inc_ref(v___y_6466_);
                                crate::leanh::lean_inc(v___x_6479_);
                                v___x_6512_ = crate::leanh::lean_apply_7(
                                    v___f_6464_,
                                    v_a_6511_,
                                    v___x_6479_,
                                    v___y_6466_,
                                    v___y_6467_,
                                    v___y_6468_,
                                    v___y_6469_,
                                    crate::leanh::lean_box(0),
                                );
                                v___y_6481_ = v___x_6512_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6479_);
                                crate::leanh::lean_dec_ref(v_decls_6472_);
                                crate::leanh::lean_dec(v___y_6469_);
                                crate::leanh::lean_dec_ref(v___y_6468_);
                                crate::leanh::lean_dec(v___y_6467_);
                                crate::leanh::lean_dec_ref(v___y_6466_);
                                crate::leanh::lean_dec_ref(v___f_6464_);
                                v_a_6513_ = crate::leanh::lean_ctor_get(v___x_6510_, 0);
                                v_isSharedCheck_6520_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6510_)) as u8;
                                if v_isSharedCheck_6520_ == 0 {
                                    v___x_6515_ = v___x_6510_;
                                    v_isShared_6516_ = v_isSharedCheck_6520_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6513_);
                                    crate::leanh::lean_dec(v___x_6510_);
                                    v___x_6515_ = crate::leanh::lean_box(0);
                                    v_isShared_6516_ = v_isSharedCheck_6520_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6474_);
                        crate::leanh::lean_dec_ref(v_decls_6472_);
                        crate::leanh::lean_dec(v___y_6469_);
                        crate::leanh::lean_dec_ref(v___y_6468_);
                        crate::leanh::lean_dec(v___y_6467_);
                        crate::leanh::lean_dec_ref(v___y_6466_);
                        crate::leanh::lean_dec_ref(v___f_6465_);
                        crate::leanh::lean_dec_ref(v___f_6464_);
                        v_a_6521_ = crate::leanh::lean_ctor_get(v___x_6475_, 0);
                        v_isSharedCheck_6528_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6475_)) as u8;
                        if v_isSharedCheck_6528_ == 0 {
                            v___x_6523_ = v___x_6475_;
                            v_isShared_6524_ = v_isSharedCheck_6528_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6521_);
                            crate::leanh::lean_dec(v___x_6475_);
                            v___x_6523_ = crate::leanh::lean_box(0);
                            v_isShared_6524_ = v_isSharedCheck_6528_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decls_6472_);
                    crate::leanh::lean_dec(v___y_6469_);
                    crate::leanh::lean_dec_ref(v___y_6468_);
                    crate::leanh::lean_dec(v___y_6467_);
                    crate::leanh::lean_dec_ref(v___y_6466_);
                    crate::leanh::lean_dec_ref(v___f_6465_);
                    crate::leanh::lean_dec_ref(v___f_6464_);
                    crate::leanh::lean_dec(v_mvarId_6463_);
                    v_a_6529_ = crate::leanh::lean_ctor_get(v___x_6473_, 0);
                    v_isSharedCheck_6536_ = (!crate::leanh::lean_is_exclusive(v___x_6473_)) as u8;
                    if v_isSharedCheck_6536_ == 0 {
                        v___x_6531_ = v___x_6473_;
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6529_);
                        crate::leanh::lean_dec(v___x_6473_);
                        v___x_6531_ = crate::leanh::lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_6481_) == 0 {
                    v_a_6482_ = crate::leanh::lean_ctor_get(v___y_6481_, 0);
                    v_isSharedCheck_6496_ = (!crate::leanh::lean_is_exclusive(v___y_6481_)) as u8;
                    if v_isSharedCheck_6496_ == 0 {
                        v___x_6484_ = v___y_6481_;
                        v_isShared_6485_ = v_isSharedCheck_6496_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6482_);
                        crate::leanh::lean_dec(v___y_6481_);
                        v___x_6484_ = crate::leanh::lean_box(0);
                        v_isShared_6485_ = v_isSharedCheck_6496_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6479_);
                    crate::leanh::lean_dec_ref(v_decls_6472_);
                    crate::leanh::lean_dec(v___y_6469_);
                    crate::leanh::lean_dec_ref(v___y_6468_);
                    crate::leanh::lean_dec(v___y_6467_);
                    crate::leanh::lean_dec_ref(v___y_6466_);
                    v_a_6497_ = crate::leanh::lean_ctor_get(v___y_6481_, 0);
                    v_isSharedCheck_6504_ = (!crate::leanh::lean_is_exclusive(v___y_6481_)) as u8;
                    if v_isSharedCheck_6504_ == 0 {
                        v___x_6499_ = v___y_6481_;
                        v_isShared_6500_ = v_isSharedCheck_6504_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6497_);
                        crate::leanh::lean_dec(v___y_6481_);
                        v___x_6499_ = crate::leanh::lean_box(0);
                        v_isShared_6500_ = v_isSharedCheck_6504_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6486_ = lean_st_ref_get(v___x_6479_);
                crate::leanh::lean_dec(v___x_6479_);
                crate::leanh::lean_dec(v___x_6486_);
                v_size_6487_ = crate::leanh::lean_ctor_get(v_a_6482_, 0);
                v___x_6488_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6489_ = lean_nat_dec_eq(v_size_6487_, v___x_6488_);
                if v___x_6489_ == 0 {
                    crate::leanh::lean_del_object(v___x_6484_);
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
                    crate::leanh::lean_dec(v___y_6469_);
                    crate::leanh::lean_dec_ref(v___y_6468_);
                    crate::leanh::lean_dec(v___y_6467_);
                    crate::leanh::lean_dec_ref(v___y_6466_);
                    crate::leanh::lean_dec_ref(v_decls_6472_);
                    crate::leanh::lean_dec(v_a_6482_);
                    return v___x_6491_;
                } else {
                    crate::leanh::lean_dec(v_a_6482_);
                    crate::leanh::lean_dec_ref(v_decls_6472_);
                    crate::leanh::lean_dec(v___y_6469_);
                    crate::leanh::lean_dec_ref(v___y_6468_);
                    crate::leanh::lean_dec(v___y_6467_);
                    crate::leanh::lean_dec_ref(v___y_6466_);
                    v___x_6492_ = l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0;
                    if v_isShared_6485_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6484_, 0, v___x_6492_);
                        v___x_6494_ = v___x_6484_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6495_, 0, v___x_6492_);
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
                    v_reuseFailAlloc_6503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6503_, 0, v_a_6497_);
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
                    v_reuseFailAlloc_6519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6519_, 0, v_a_6513_);
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
                    v_reuseFailAlloc_6527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6521_);
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
                    v_reuseFailAlloc_6535_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6535_, 0, v_a_6529_);
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
    mut v_candidates_6537_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6538_: *mut crate::leanh::LeanObject,
    mut v___f_6539_: *mut crate::leanh::LeanObject,
    mut v___f_6540_: *mut crate::leanh::LeanObject,
    mut v___y_6541_: *mut crate::leanh::LeanObject,
    mut v___y_6542_: *mut crate::leanh::LeanObject,
    mut v___y_6543_: *mut crate::leanh::LeanObject,
    mut v___y_6544_: *mut crate::leanh::LeanObject,
    mut v___y_6545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_6549_: *mut crate::leanh::LeanObject,
    mut v_a_6550_: *mut crate::leanh::LeanObject,
    mut v_a_6551_: *mut crate::leanh::LeanObject,
    mut v_a_6552_: *mut crate::leanh::LeanObject,
    mut v_a_6553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6555_ = l_Lean_MVarId_getNondepPropHyps___closed__0;
    v___f_6556_ = l_Lean_MVarId_getNondepPropHyps___closed__1;
    v_candidates_6557_ = l_Lean_instEmptyCollectionFVarIdHashSet;
    crate::leanh::lean_inc(v_mvarId_6549_);
    v___f_6558_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_getNondepPropHyps___lam__2___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6558_, 0, v_candidates_6557_);
    crate::leanh::lean_closure_set(v___f_6558_, 1, v_mvarId_6549_);
    crate::leanh::lean_closure_set(v___f_6558_, 2, v___f_6556_);
    crate::leanh::lean_closure_set(v___f_6558_, 3, v___f_6555_);
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
    mut v_mvarId_6560_: *mut crate::leanh::LeanObject,
    mut v_a_6561_: *mut crate::leanh::LeanObject,
    mut v_a_6562_: *mut crate::leanh::LeanObject,
    mut v_a_6563_: *mut crate::leanh::LeanObject,
    mut v_a_6564_: *mut crate::leanh::LeanObject,
    mut v_a_6565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6566_ =
        l_Lean_MVarId_getNondepPropHyps(v_mvarId_6560_, v_a_6561_, v_a_6562_, v_a_6563_, v_a_6564_);
    crate::leanh::lean_dec(v_a_6564_);
    crate::leanh::lean_dec_ref(v_a_6563_);
    crate::leanh::lean_dec(v_a_6562_);
    crate::leanh::lean_dec_ref(v_a_6561_);
    return v_res_6566_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(
    mut v_00_u03b2_6567_: *mut crate::leanh::LeanObject,
    mut v_m_6568_: *mut crate::leanh::LeanObject,
    mut v_a_6569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6570_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_6568_, v_a_6569_);
    return v___x_6570_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(
    mut v_00_u03b2_6571_: *mut crate::leanh::LeanObject,
    mut v_m_6572_: *mut crate::leanh::LeanObject,
    mut v_a_6573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6574_ =
        l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(
            v_00_u03b2_6571_,
            v_m_6572_,
            v_a_6573_,
        );
    crate::leanh::lean_dec(v_a_6573_);
    return v_res_6574_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(
    mut v_00_u03b2_6575_: *mut crate::leanh::LeanObject,
    mut v_m_6576_: *mut crate::leanh::LeanObject,
    mut v_a_6577_: *mut crate::leanh::LeanObject,
    mut v_b_6578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6579_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_6576_, v_a_6577_, v_b_6578_);
    return v___x_6579_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(
    mut v_00_u03b2_6580_: *mut crate::leanh::LeanObject,
    mut v_m_6581_: *mut crate::leanh::LeanObject,
    mut v_a_6582_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6583_: u8 = 0;
    v___x_6583_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_6581_, v_a_6582_);
    return v___x_6583_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(
    mut v_00_u03b2_6584_: *mut crate::leanh::LeanObject,
    mut v_m_6585_: *mut crate::leanh::LeanObject,
    mut v_a_6586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6587_: u8 = 0;
    let mut v_r_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6587_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(
            v_00_u03b2_6584_,
            v_m_6585_,
            v_a_6586_,
        );
    crate::leanh::lean_dec(v_a_6586_);
    crate::leanh::lean_dec_ref(v_m_6585_);
    v_r_6588_ = crate::leanh::lean_box((v_res_6587_) as usize);
    return v_r_6588_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(
    mut v_00_u03b2_6589_: *mut crate::leanh::LeanObject,
    mut v_a_6590_: *mut crate::leanh::LeanObject,
    mut v_x_6591_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6592_: u8 = 0;
    v___x_6592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_6590_, v_x_6591_);
    return v___x_6592_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(
    mut v_00_u03b2_6593_: *mut crate::leanh::LeanObject,
    mut v_a_6594_: *mut crate::leanh::LeanObject,
    mut v_x_6595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6596_: u8 = 0;
    let mut v_r_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_6593_, v_a_6594_, v_x_6595_);
    crate::leanh::lean_dec(v_x_6595_);
    crate::leanh::lean_dec(v_a_6594_);
    v_r_6597_ = crate::leanh::lean_box((v_res_6596_) as usize);
    return v_r_6597_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(
    mut v_00_u03b2_6598_: *mut crate::leanh::LeanObject,
    mut v_a_6599_: *mut crate::leanh::LeanObject,
    mut v_x_6600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6601_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_6599_, v_x_6600_);
    return v___x_6601_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(
    mut v_00_u03b2_6602_: *mut crate::leanh::LeanObject,
    mut v_a_6603_: *mut crate::leanh::LeanObject,
    mut v_x_6604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6605_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_6602_, v_a_6603_, v_x_6604_);
    crate::leanh::lean_dec(v_a_6603_);
    return v_res_6605_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(
    mut v_e_6606_: *mut crate::leanh::LeanObject,
    mut v_a_6607_: *mut crate::leanh::LeanObject,
    mut v___y_6608_: *mut crate::leanh::LeanObject,
    mut v___y_6609_: *mut crate::leanh::LeanObject,
    mut v___y_6610_: *mut crate::leanh::LeanObject,
    mut v___y_6611_: *mut crate::leanh::LeanObject,
    mut v___y_6612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6614_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_6606_, v_a_6607_);
    return v___x_6614_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(
    mut v_e_6615_: *mut crate::leanh::LeanObject,
    mut v_a_6616_: *mut crate::leanh::LeanObject,
    mut v___y_6617_: *mut crate::leanh::LeanObject,
    mut v___y_6618_: *mut crate::leanh::LeanObject,
    mut v___y_6619_: *mut crate::leanh::LeanObject,
    mut v___y_6620_: *mut crate::leanh::LeanObject,
    mut v___y_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6623_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_6615_, v_a_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_);
    crate::leanh::lean_dec(v___y_6621_);
    crate::leanh::lean_dec_ref(v___y_6620_);
    crate::leanh::lean_dec(v___y_6619_);
    crate::leanh::lean_dec_ref(v___y_6618_);
    crate::leanh::lean_dec(v___y_6617_);
    crate::leanh::lean_dec(v_a_6616_);
    return v_res_6623_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(
    mut v_00_u03b2_6624_: *mut crate::leanh::LeanObject,
    mut v_data_6625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_6625_);
    return v___x_6626_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(
    mut v_e_6627_: *mut crate::leanh::LeanObject,
    mut v_a_6628_: *mut crate::leanh::LeanObject,
    mut v___y_6629_: *mut crate::leanh::LeanObject,
    mut v___y_6630_: *mut crate::leanh::LeanObject,
    mut v___y_6631_: *mut crate::leanh::LeanObject,
    mut v___y_6632_: *mut crate::leanh::LeanObject,
    mut v___y_6633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6635_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_6627_, v_a_6628_);
    return v___x_6635_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(
    mut v_e_6636_: *mut crate::leanh::LeanObject,
    mut v_a_6637_: *mut crate::leanh::LeanObject,
    mut v___y_6638_: *mut crate::leanh::LeanObject,
    mut v___y_6639_: *mut crate::leanh::LeanObject,
    mut v___y_6640_: *mut crate::leanh::LeanObject,
    mut v___y_6641_: *mut crate::leanh::LeanObject,
    mut v___y_6642_: *mut crate::leanh::LeanObject,
    mut v___y_6643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6644_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_6636_, v_a_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_, v___y_6642_);
    crate::leanh::lean_dec(v___y_6642_);
    crate::leanh::lean_dec_ref(v___y_6641_);
    crate::leanh::lean_dec(v___y_6640_);
    crate::leanh::lean_dec_ref(v___y_6639_);
    crate::leanh::lean_dec(v___y_6638_);
    crate::leanh::lean_dec(v_a_6637_);
    return v_res_6644_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(
    mut v_00_u03b2_6645_: *mut crate::leanh::LeanObject,
    mut v_i_6646_: *mut crate::leanh::LeanObject,
    mut v_source_6647_: *mut crate::leanh::LeanObject,
    mut v_target_6648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_6646_, v_source_6647_, v_target_6648_);
    return v___x_6649_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(
    mut v_a_6650_: *mut crate::leanh::LeanObject,
    mut v_as_6651_: *mut crate::leanh::LeanObject,
    mut v_sz_6652_: usize,
    mut v_i_6653_: usize,
    mut v_b_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
    mut v___y_6656_: *mut crate::leanh::LeanObject,
    mut v___y_6657_: *mut crate::leanh::LeanObject,
    mut v___y_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_6650_, v_as_6651_, v_sz_6652_, v_i_6653_, v_b_6654_);
    return v___x_6660_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(
    mut v_a_6661_: *mut crate::leanh::LeanObject,
    mut v_as_6662_: *mut crate::leanh::LeanObject,
    mut v_sz_6663_: *mut crate::leanh::LeanObject,
    mut v_i_6664_: *mut crate::leanh::LeanObject,
    mut v_b_6665_: *mut crate::leanh::LeanObject,
    mut v___y_6666_: *mut crate::leanh::LeanObject,
    mut v___y_6667_: *mut crate::leanh::LeanObject,
    mut v___y_6668_: *mut crate::leanh::LeanObject,
    mut v___y_6669_: *mut crate::leanh::LeanObject,
    mut v___y_6670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6671_: usize = 0;
    let mut v_i_boxed_6672_: usize = 0;
    let mut v_res_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6671_ = crate::leanh::lean_unbox_usize(v_sz_6663_);
    crate::leanh::lean_dec(v_sz_6663_);
    v_i_boxed_6672_ = crate::leanh::lean_unbox_usize(v_i_6664_);
    crate::leanh::lean_dec(v_i_6664_);
    v_res_6673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_6661_, v_as_6662_, v_sz_boxed_6671_, v_i_boxed_6672_, v_b_6665_, v___y_6666_, v___y_6667_, v___y_6668_, v___y_6669_);
    crate::leanh::lean_dec(v___y_6669_);
    crate::leanh::lean_dec_ref(v___y_6668_);
    crate::leanh::lean_dec(v___y_6667_);
    crate::leanh::lean_dec_ref(v___y_6666_);
    crate::leanh::lean_dec_ref(v_as_6662_);
    crate::leanh::lean_dec_ref(v_a_6661_);
    return v_res_6673_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(
    mut v_00_u03b2_6674_: *mut crate::leanh::LeanObject,
    mut v_m_6675_: *mut crate::leanh::LeanObject,
    mut v_a_6676_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6677_: u8 = 0;
    v___x_6677_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_6675_, v_a_6676_);
    return v___x_6677_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(
    mut v_00_u03b2_6678_: *mut crate::leanh::LeanObject,
    mut v_m_6679_: *mut crate::leanh::LeanObject,
    mut v_a_6680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6681_: u8 = 0;
    let mut v_r_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6681_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_6678_, v_m_6679_, v_a_6680_);
    crate::leanh::lean_dec_ref(v_a_6680_);
    crate::leanh::lean_dec_ref(v_m_6679_);
    v_r_6682_ = crate::leanh::lean_box((v_res_6681_) as usize);
    return v_r_6682_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(
    mut v_00_u03b2_6683_: *mut crate::leanh::LeanObject,
    mut v_m_6684_: *mut crate::leanh::LeanObject,
    mut v_a_6685_: *mut crate::leanh::LeanObject,
    mut v_b_6686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6687_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_6684_, v_a_6685_, v_b_6686_);
    return v___x_6687_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(
    mut v_00_u03b2_6688_: *mut crate::leanh::LeanObject,
    mut v_x_6689_: *mut crate::leanh::LeanObject,
    mut v_x_6690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6691_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_6689_, v_x_6690_);
    return v___x_6691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(
    mut v_a_6692_: *mut crate::leanh::LeanObject,
    mut v_as_6693_: *mut crate::leanh::LeanObject,
    mut v_sz_6694_: usize,
    mut v_i_6695_: usize,
    mut v_b_6696_: *mut crate::leanh::LeanObject,
    mut v___y_6697_: *mut crate::leanh::LeanObject,
    mut v___y_6698_: *mut crate::leanh::LeanObject,
    mut v___y_6699_: *mut crate::leanh::LeanObject,
    mut v___y_6700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_6692_, v_as_6693_, v_sz_6694_, v_i_6695_, v_b_6696_);
    return v___x_6702_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(
    mut v_a_6703_: *mut crate::leanh::LeanObject,
    mut v_as_6704_: *mut crate::leanh::LeanObject,
    mut v_sz_6705_: *mut crate::leanh::LeanObject,
    mut v_i_6706_: *mut crate::leanh::LeanObject,
    mut v_b_6707_: *mut crate::leanh::LeanObject,
    mut v___y_6708_: *mut crate::leanh::LeanObject,
    mut v___y_6709_: *mut crate::leanh::LeanObject,
    mut v___y_6710_: *mut crate::leanh::LeanObject,
    mut v___y_6711_: *mut crate::leanh::LeanObject,
    mut v___y_6712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6713_: usize = 0;
    let mut v_i_boxed_6714_: usize = 0;
    let mut v_res_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6713_ = crate::leanh::lean_unbox_usize(v_sz_6705_);
    crate::leanh::lean_dec(v_sz_6705_);
    v_i_boxed_6714_ = crate::leanh::lean_unbox_usize(v_i_6706_);
    crate::leanh::lean_dec(v_i_6706_);
    v_res_6715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_6703_, v_as_6704_, v_sz_boxed_6713_, v_i_boxed_6714_, v_b_6707_, v___y_6708_, v___y_6709_, v___y_6710_, v___y_6711_);
    crate::leanh::lean_dec(v___y_6711_);
    crate::leanh::lean_dec_ref(v___y_6710_);
    crate::leanh::lean_dec(v___y_6709_);
    crate::leanh::lean_dec_ref(v___y_6708_);
    crate::leanh::lean_dec_ref(v_as_6704_);
    crate::leanh::lean_dec_ref(v_a_6703_);
    return v_res_6715_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(
    mut v_00_u03b2_6716_: *mut crate::leanh::LeanObject,
    mut v_a_6717_: *mut crate::leanh::LeanObject,
    mut v_x_6718_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6719_: u8 = 0;
    v___x_6719_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_6717_, v_x_6718_);
    return v___x_6719_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(
    mut v_00_u03b2_6720_: *mut crate::leanh::LeanObject,
    mut v_a_6721_: *mut crate::leanh::LeanObject,
    mut v_x_6722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6723_: u8 = 0;
    let mut v_r_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6723_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_6720_, v_a_6721_, v_x_6722_);
    crate::leanh::lean_dec(v_x_6722_);
    crate::leanh::lean_dec_ref(v_a_6721_);
    v_r_6724_ = crate::leanh::lean_box((v_res_6723_) as usize);
    return v_r_6724_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(
    mut v_00_u03b2_6725_: *mut crate::leanh::LeanObject,
    mut v_data_6726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_6726_);
    return v___x_6727_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(
    mut v_00_u03b2_6728_: *mut crate::leanh::LeanObject,
    mut v_i_6729_: *mut crate::leanh::LeanObject,
    mut v_source_6730_: *mut crate::leanh::LeanObject,
    mut v_target_6731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6732_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_6729_, v_source_6730_, v_target_6731_);
    return v___x_6732_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(
    mut v_00_u03b2_6733_: *mut crate::leanh::LeanObject,
    mut v_x_6734_: *mut crate::leanh::LeanObject,
    mut v_x_6735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6736_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_6734_, v_x_6735_);
    return v___x_6736_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6742_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6743_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6743_, 0, v___x_6742_);
    return v___x_6743_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6744_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
    v___x_6745_ = l_Lean_MessageData_ofFormat(v___x_6744_);
    return v___x_6745_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6746_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
    v___x_6747_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2;
    v___x_6748_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6748_, 0, v___x_6747_);
    crate::leanh::lean_ctor_set(v___x_6748_, 1, v___x_6746_);
    return v___x_6748_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(
    mut v_ref_6749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6751_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
    v___x_6752_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6752_, 0, v_ref_6749_);
    crate::leanh::lean_ctor_set(v___x_6752_, 1, v___x_6751_);
    v___x_6753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6753_, 0, v___x_6752_);
    return v___x_6753_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(
    mut v_ref_6754_: *mut crate::leanh::LeanObject,
    mut v___y_6755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6756_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_6754_);
    return v_res_6756_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(
    mut v_00_u03b1_6757_: *mut crate::leanh::LeanObject,
    mut v_ref_6758_: *mut crate::leanh::LeanObject,
    mut v___y_6759_: *mut crate::leanh::LeanObject,
    mut v___y_6760_: *mut crate::leanh::LeanObject,
    mut v___y_6761_: *mut crate::leanh::LeanObject,
    mut v___y_6762_: *mut crate::leanh::LeanObject,
    mut v___y_6763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6765_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_6758_);
    return v___x_6765_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(
    mut v_00_u03b1_6766_: *mut crate::leanh::LeanObject,
    mut v_ref_6767_: *mut crate::leanh::LeanObject,
    mut v___y_6768_: *mut crate::leanh::LeanObject,
    mut v___y_6769_: *mut crate::leanh::LeanObject,
    mut v___y_6770_: *mut crate::leanh::LeanObject,
    mut v___y_6771_: *mut crate::leanh::LeanObject,
    mut v___y_6772_: *mut crate::leanh::LeanObject,
    mut v___y_6773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6774_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_6766_, v_ref_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_);
    crate::leanh::lean_dec(v___y_6772_);
    crate::leanh::lean_dec_ref(v___y_6771_);
    crate::leanh::lean_dec(v___y_6770_);
    crate::leanh::lean_dec_ref(v___y_6769_);
    crate::leanh::lean_dec(v___y_6768_);
    return v_res_6774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(
    mut v_x_6775_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6776_: *mut crate::leanh::LeanObject,
    mut v_a_6777_: *mut crate::leanh::LeanObject,
    mut v_a_6778_: *mut crate::leanh::LeanObject,
    mut v_a_6779_: *mut crate::leanh::LeanObject,
    mut v_a_6780_: *mut crate::leanh::LeanObject,
    mut v_a_6781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6795_: u8 = 0;
    let mut v_cancelTk_x3f_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6797_: u8 = 0;
    let mut v_inheritedTraceOptions_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6807_: u8 = 0;
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6817_: u8 = 0;
    let mut v_a_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6821_: u8 = 0;
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6825_: u8 = 0;
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: u8 = 0;
    let mut v___x_6828_: u8 = 0;
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6783_ = crate::leanh::lean_ctor_get(v_a_6780_, 0);
                v_fileMap_6784_ = crate::leanh::lean_ctor_get(v_a_6780_, 1);
                v_options_6785_ = crate::leanh::lean_ctor_get(v_a_6780_, 2);
                v_currRecDepth_6786_ = crate::leanh::lean_ctor_get(v_a_6780_, 3);
                v_maxRecDepth_6787_ = crate::leanh::lean_ctor_get(v_a_6780_, 4);
                v_ref_6788_ = crate::leanh::lean_ctor_get(v_a_6780_, 5);
                v_currNamespace_6789_ = crate::leanh::lean_ctor_get(v_a_6780_, 6);
                v_openDecls_6790_ = crate::leanh::lean_ctor_get(v_a_6780_, 7);
                v_initHeartbeats_6791_ = crate::leanh::lean_ctor_get(v_a_6780_, 8);
                v_maxHeartbeats_6792_ = crate::leanh::lean_ctor_get(v_a_6780_, 9);
                v_quotContext_6793_ = crate::leanh::lean_ctor_get(v_a_6780_, 10);
                v_currMacroScope_6794_ = crate::leanh::lean_ctor_get(v_a_6780_, 11);
                v_diag_6795_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6780_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6796_ = crate::leanh::lean_ctor_get(v_a_6780_, 12);
                v_suppressElabErrors_6797_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6780_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6798_ = crate::leanh::lean_ctor_get(v_a_6780_, 13);
                v___x_6826_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6827_ = lean_nat_dec_eq(v_maxRecDepth_6787_, v___x_6826_);
                if v___x_6827_ == 0 {
                    v___x_6828_ = lean_nat_dec_eq(v_currRecDepth_6786_, v_maxRecDepth_6787_);
                    if v___x_6828_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_mvarId_6776_);
                        crate::leanh::lean_dec_ref(v_x_6775_);
                        crate::leanh::lean_inc(v_ref_6788_);
                        v___x_6829_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_6788_);
                        return v___x_6829_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6800_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6801_ = lean_nat_add(v_currRecDepth_6786_, v___x_6800_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6798_);
                crate::leanh::lean_inc(v_cancelTk_x3f_6796_);
                crate::leanh::lean_inc(v_currMacroScope_6794_);
                crate::leanh::lean_inc(v_quotContext_6793_);
                crate::leanh::lean_inc(v_maxHeartbeats_6792_);
                crate::leanh::lean_inc(v_initHeartbeats_6791_);
                crate::leanh::lean_inc(v_openDecls_6790_);
                crate::leanh::lean_inc(v_currNamespace_6789_);
                crate::leanh::lean_inc(v_ref_6788_);
                crate::leanh::lean_inc(v_maxRecDepth_6787_);
                crate::leanh::lean_inc_ref(v_options_6785_);
                crate::leanh::lean_inc_ref(v_fileMap_6784_);
                crate::leanh::lean_inc_ref(v_fileName_6783_);
                v___x_6802_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_6802_, 0, v_fileName_6783_);
                crate::leanh::lean_ctor_set(v___x_6802_, 1, v_fileMap_6784_);
                crate::leanh::lean_ctor_set(v___x_6802_, 2, v_options_6785_);
                crate::leanh::lean_ctor_set(v___x_6802_, 3, v___x_6801_);
                crate::leanh::lean_ctor_set(v___x_6802_, 4, v_maxRecDepth_6787_);
                crate::leanh::lean_ctor_set(v___x_6802_, 5, v_ref_6788_);
                crate::leanh::lean_ctor_set(v___x_6802_, 6, v_currNamespace_6789_);
                crate::leanh::lean_ctor_set(v___x_6802_, 7, v_openDecls_6790_);
                crate::leanh::lean_ctor_set(v___x_6802_, 8, v_initHeartbeats_6791_);
                crate::leanh::lean_ctor_set(v___x_6802_, 9, v_maxHeartbeats_6792_);
                crate::leanh::lean_ctor_set(v___x_6802_, 10, v_quotContext_6793_);
                crate::leanh::lean_ctor_set(v___x_6802_, 11, v_currMacroScope_6794_);
                crate::leanh::lean_ctor_set(v___x_6802_, 12, v_cancelTk_x3f_6796_);
                crate::leanh::lean_ctor_set(v___x_6802_, 13, v_inheritedTraceOptions_6798_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6802_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_6795_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6802_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6797_,
                );
                crate::leanh::lean_inc_ref(v_x_6775_);
                crate::leanh::lean_inc(v_a_6781_);
                crate::leanh::lean_inc_ref(v___x_6802_);
                crate::leanh::lean_inc(v_a_6779_);
                crate::leanh::lean_inc_ref(v_a_6778_);
                crate::leanh::lean_inc(v_mvarId_6776_);
                v___x_6803_ = crate::leanh::lean_apply_6(
                    v_x_6775_,
                    v_mvarId_6776_,
                    v_a_6778_,
                    v_a_6779_,
                    v___x_6802_,
                    v_a_6781_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6803_) == 0 {
                    v_a_6804_ = crate::leanh::lean_ctor_get(v___x_6803_, 0);
                    v_isSharedCheck_6817_ = (!crate::leanh::lean_is_exclusive(v___x_6803_)) as u8;
                    if v_isSharedCheck_6817_ == 0 {
                        v___x_6806_ = v___x_6803_;
                        v_isShared_6807_ = v_isSharedCheck_6817_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6804_);
                        crate::leanh::lean_dec(v___x_6803_);
                        v___x_6806_ = crate::leanh::lean_box(0);
                        v_isShared_6807_ = v_isSharedCheck_6817_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_6802_, 14);
                    crate::leanh::lean_dec(v_mvarId_6776_);
                    crate::leanh::lean_dec_ref(v_x_6775_);
                    v_a_6818_ = crate::leanh::lean_ctor_get(v___x_6803_, 0);
                    v_isSharedCheck_6825_ = (!crate::leanh::lean_is_exclusive(v___x_6803_)) as u8;
                    if v_isSharedCheck_6825_ == 0 {
                        v___x_6820_ = v___x_6803_;
                        v_isShared_6821_ = v_isSharedCheck_6825_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6818_);
                        crate::leanh::lean_dec(v___x_6803_);
                        v___x_6820_ = crate::leanh::lean_box(0);
                        v_isShared_6821_ = v_isSharedCheck_6825_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6804_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6802_, 14);
                    crate::leanh::lean_dec_ref(v_x_6775_);
                    v___x_6808_ = lean_st_ref_take(v_a_6777_);
                    v___x_6809_ = lean_array_push(v___x_6808_, v_mvarId_6776_);
                    v___x_6810_ = lean_st_ref_set(v_a_6777_, v___x_6809_);
                    v___x_6811_ = crate::leanh::lean_box(0);
                    if v_isShared_6807_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6806_, 0, v___x_6811_);
                        v___x_6813_ = v___x_6806_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6814_, 0, v___x_6811_);
                        v___x_6813_ = v_reuseFailAlloc_6814_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6806_);
                    crate::leanh::lean_dec(v_mvarId_6776_);
                    v_val_6815_ = crate::leanh::lean_ctor_get(v_a_6804_, 0);
                    crate::leanh::lean_inc(v_val_6815_);
                    crate::leanh::lean_dec_ref_known(v_a_6804_, 1);
                    v___x_6816_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_6775_, v_val_6815_, v_a_6777_, v_a_6778_, v_a_6779_, v___x_6802_, v_a_6781_);
                    crate::leanh::lean_dec_ref_known(v___x_6802_, 14);
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
                    v_reuseFailAlloc_6824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6824_, 0, v_a_6818_);
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
    mut v_x_6830_: *mut crate::leanh::LeanObject,
    mut v_as_6831_: *mut crate::leanh::LeanObject,
    mut v___y_6832_: *mut crate::leanh::LeanObject,
    mut v___y_6833_: *mut crate::leanh::LeanObject,
    mut v___y_6834_: *mut crate::leanh::LeanObject,
    mut v___y_6835_: *mut crate::leanh::LeanObject,
    mut v___y_6836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_6831_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_6830_);
                    v___x_6838_ = crate::leanh::lean_box(0);
                    v___x_6839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6839_, 0, v___x_6838_);
                    return v___x_6839_;
                } else {
                    v_head_6840_ = crate::leanh::lean_ctor_get(v_as_6831_, 0);
                    crate::leanh::lean_inc(v_head_6840_);
                    v_tail_6841_ = crate::leanh::lean_ctor_get(v_as_6831_, 1);
                    crate::leanh::lean_inc(v_tail_6841_);
                    crate::leanh::lean_dec_ref_known(v_as_6831_, 2);
                    crate::leanh::lean_inc_ref(v_x_6830_);
                    v___x_6842_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(
                        v_x_6830_,
                        v_head_6840_,
                        v___y_6832_,
                        v___y_6833_,
                        v___y_6834_,
                        v___y_6835_,
                        v___y_6836_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6842_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6842_, 1);
                        v_as_6831_ = v_tail_6841_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_6841_);
                        crate::leanh::lean_dec_ref(v_x_6830_);
                        return v___x_6842_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(
    mut v_x_6844_: *mut crate::leanh::LeanObject,
    mut v_as_6845_: *mut crate::leanh::LeanObject,
    mut v___y_6846_: *mut crate::leanh::LeanObject,
    mut v___y_6847_: *mut crate::leanh::LeanObject,
    mut v___y_6848_: *mut crate::leanh::LeanObject,
    mut v___y_6849_: *mut crate::leanh::LeanObject,
    mut v___y_6850_: *mut crate::leanh::LeanObject,
    mut v___y_6851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_6850_);
    crate::leanh::lean_dec_ref(v___y_6849_);
    crate::leanh::lean_dec(v___y_6848_);
    crate::leanh::lean_dec_ref(v___y_6847_);
    crate::leanh::lean_dec(v___y_6846_);
    return v_res_6852_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(
    mut v_x_6853_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6854_: *mut crate::leanh::LeanObject,
    mut v_a_6855_: *mut crate::leanh::LeanObject,
    mut v_a_6856_: *mut crate::leanh::LeanObject,
    mut v_a_6857_: *mut crate::leanh::LeanObject,
    mut v_a_6858_: *mut crate::leanh::LeanObject,
    mut v_a_6859_: *mut crate::leanh::LeanObject,
    mut v_a_6860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6861_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(
        v_x_6853_,
        v_mvarId_6854_,
        v_a_6855_,
        v_a_6856_,
        v_a_6857_,
        v_a_6858_,
        v_a_6859_,
    );
    crate::leanh::lean_dec(v_a_6859_);
    crate::leanh::lean_dec_ref(v_a_6858_);
    crate::leanh::lean_dec(v_a_6857_);
    crate::leanh::lean_dec_ref(v_a_6856_);
    crate::leanh::lean_dec(v_a_6855_);
    return v_res_6861_;
}
pub unsafe fn l_Lean_Meta_saturate(
    mut v_mvarId_6862_: *mut crate::leanh::LeanObject,
    mut v_x_6863_: *mut crate::leanh::LeanObject,
    mut v_a_6864_: *mut crate::leanh::LeanObject,
    mut v_a_6865_: *mut crate::leanh::LeanObject,
    mut v_a_6866_: *mut crate::leanh::LeanObject,
    mut v_a_6867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6874_: u8 = 0;
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6880_: u8 = 0;
    let mut v_unused_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6885_: u8 = 0;
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_6871_) == 0 {
                    v_isSharedCheck_6880_ = (!crate::leanh::lean_is_exclusive(v___x_6871_)) as u8;
                    if v_isSharedCheck_6880_ == 0 {
                        v_unused_6881_ = crate::leanh::lean_ctor_get(v___x_6871_, 0);
                        crate::leanh::lean_dec(v_unused_6881_);
                        v___x_6873_ = v___x_6871_;
                        v_isShared_6874_ = v_isSharedCheck_6880_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6871_);
                        v___x_6873_ = crate::leanh::lean_box(0);
                        v_isShared_6874_ = v_isSharedCheck_6880_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6870_);
                    v_a_6882_ = crate::leanh::lean_ctor_get(v___x_6871_, 0);
                    v_isSharedCheck_6889_ = (!crate::leanh::lean_is_exclusive(v___x_6871_)) as u8;
                    if v_isSharedCheck_6889_ == 0 {
                        v___x_6884_ = v___x_6871_;
                        v_isShared_6885_ = v_isSharedCheck_6889_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6882_);
                        crate::leanh::lean_dec(v___x_6871_);
                        v___x_6884_ = crate::leanh::lean_box(0);
                        v_isShared_6885_ = v_isSharedCheck_6889_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6875_ = lean_st_ref_get(v___x_6870_);
                crate::leanh::lean_dec(v___x_6870_);
                v___x_6876_ = lean_array_to_list(v___x_6875_);
                if v_isShared_6874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6873_, 0, v___x_6876_);
                    v___x_6878_ = v___x_6873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6879_, 0, v___x_6876_);
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
                    v_reuseFailAlloc_6888_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6888_, 0, v_a_6882_);
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
    mut v_mvarId_6890_: *mut crate::leanh::LeanObject,
    mut v_x_6891_: *mut crate::leanh::LeanObject,
    mut v_a_6892_: *mut crate::leanh::LeanObject,
    mut v_a_6893_: *mut crate::leanh::LeanObject,
    mut v_a_6894_: *mut crate::leanh::LeanObject,
    mut v_a_6895_: *mut crate::leanh::LeanObject,
    mut v_a_6896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6897_ = l_Lean_Meta_saturate(
        v_mvarId_6890_,
        v_x_6891_,
        v_a_6892_,
        v_a_6893_,
        v_a_6894_,
        v_a_6895_,
    );
    crate::leanh::lean_dec(v_a_6895_);
    crate::leanh::lean_dec_ref(v_a_6894_);
    crate::leanh::lean_dec(v_a_6893_);
    crate::leanh::lean_dec_ref(v_a_6892_);
    return v_res_6897_;
}
pub unsafe fn l_Lean_Meta_exactlyOne(
    mut v_mvarIds_6898_: *mut crate::leanh::LeanObject,
    mut v_msg_6899_: *mut crate::leanh::LeanObject,
    mut v_a_6900_: *mut crate::leanh::LeanObject,
    mut v_a_6901_: *mut crate::leanh::LeanObject,
    mut v_a_6902_: *mut crate::leanh::LeanObject,
    mut v_a_6903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_mvarIds_6898_) == 1 {
        let mut v_tail_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_6905_ = crate::leanh::lean_ctor_get(v_mvarIds_6898_, 1);
        if crate::leanh::lean_obj_tag(v_tail_6905_) == 0 {
            let mut v_head_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_msg_6899_);
            v_head_6906_ = crate::leanh::lean_ctor_get(v_mvarIds_6898_, 0);
            crate::leanh::lean_inc(v_head_6906_);
            v___x_6907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6907_, 0, v_head_6906_);
            return v___x_6907_;
        } else {
            let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarIds_6910_: *mut crate::leanh::LeanObject,
    mut v_msg_6911_: *mut crate::leanh::LeanObject,
    mut v_a_6912_: *mut crate::leanh::LeanObject,
    mut v_a_6913_: *mut crate::leanh::LeanObject,
    mut v_a_6914_: *mut crate::leanh::LeanObject,
    mut v_a_6915_: *mut crate::leanh::LeanObject,
    mut v_a_6916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6917_ = l_Lean_Meta_exactlyOne(
        v_mvarIds_6910_,
        v_msg_6911_,
        v_a_6912_,
        v_a_6913_,
        v_a_6914_,
        v_a_6915_,
    );
    crate::leanh::lean_dec(v_a_6915_);
    crate::leanh::lean_dec_ref(v_a_6914_);
    crate::leanh::lean_dec(v_a_6913_);
    crate::leanh::lean_dec_ref(v_a_6912_);
    crate::leanh::lean_dec(v_mvarIds_6910_);
    return v_res_6917_;
}
pub unsafe fn l_Lean_Meta_ensureAtMostOne(
    mut v_mvarIds_6918_: *mut crate::leanh::LeanObject,
    mut v_msg_6919_: *mut crate::leanh::LeanObject,
    mut v_a_6920_: *mut crate::leanh::LeanObject,
    mut v_a_6921_: *mut crate::leanh::LeanObject,
    mut v_a_6922_: *mut crate::leanh::LeanObject,
    mut v_a_6923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_mvarIds_6918_) == 0 {
        let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_msg_6919_);
        v___x_6925_ = crate::leanh::lean_box(0);
        v___x_6926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6926_, 0, v___x_6925_);
        return v___x_6926_;
    } else {
        let mut v_tail_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_6927_ = crate::leanh::lean_ctor_get(v_mvarIds_6918_, 1);
        if crate::leanh::lean_obj_tag(v_tail_6927_) == 0 {
            let mut v_head_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_msg_6919_);
            v_head_6928_ = crate::leanh::lean_ctor_get(v_mvarIds_6918_, 0);
            crate::leanh::lean_inc(v_head_6928_);
            v___x_6929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6929_, 0, v_head_6928_);
            v___x_6930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6930_, 0, v___x_6929_);
            return v___x_6930_;
        } else {
            let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarIds_6932_: *mut crate::leanh::LeanObject,
    mut v_msg_6933_: *mut crate::leanh::LeanObject,
    mut v_a_6934_: *mut crate::leanh::LeanObject,
    mut v_a_6935_: *mut crate::leanh::LeanObject,
    mut v_a_6936_: *mut crate::leanh::LeanObject,
    mut v_a_6937_: *mut crate::leanh::LeanObject,
    mut v_a_6938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6939_ = l_Lean_Meta_ensureAtMostOne(
        v_mvarIds_6932_,
        v_msg_6933_,
        v_a_6934_,
        v_a_6935_,
        v_a_6936_,
        v_a_6937_,
    );
    crate::leanh::lean_dec(v_a_6937_);
    crate::leanh::lean_dec_ref(v_a_6936_);
    crate::leanh::lean_dec(v_a_6935_);
    crate::leanh::lean_dec_ref(v_a_6934_);
    crate::leanh::lean_dec(v_mvarIds_6932_);
    return v_res_6939_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(
    mut v_as_6940_: *mut crate::leanh::LeanObject,
    mut v_sz_6941_: usize,
    mut v_i_6942_: usize,
    mut v_b_6943_: *mut crate::leanh::LeanObject,
    mut v___y_6944_: *mut crate::leanh::LeanObject,
    mut v___y_6945_: *mut crate::leanh::LeanObject,
    mut v___y_6946_: *mut crate::leanh::LeanObject,
    mut v___y_6947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6954_: u8 = 0;
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: usize = 0;
    let mut v___x_6961_: usize = 0;
    let mut v_reuseFailAlloc_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: u8 = 0;
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6976_: u8 = 0;
    let mut v___x_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6980_: u8 = 0;
    let mut v_isSharedCheck_6981_: u8 = 0;
    let mut v_unused_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6949_ = lean_usize_dec_lt(v_i_6942_, v_sz_6941_);
                if v___x_6949_ == 0 {
                    v___x_6950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6950_, 0, v_b_6943_);
                    return v___x_6950_;
                } else {
                    v_snd_6951_ = crate::leanh::lean_ctor_get(v_b_6943_, 1);
                    v_isSharedCheck_6981_ = (!crate::leanh::lean_is_exclusive(v_b_6943_)) as u8;
                    if v_isSharedCheck_6981_ == 0 {
                        v_unused_6982_ = crate::leanh::lean_ctor_get(v_b_6943_, 0);
                        crate::leanh::lean_dec(v_unused_6982_);
                        v___x_6953_ = v_b_6943_;
                        v_isShared_6954_ = v_isSharedCheck_6981_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6951_);
                        crate::leanh::lean_dec(v_b_6943_);
                        v___x_6953_ = crate::leanh::lean_box(0);
                        v_isShared_6954_ = v_isSharedCheck_6981_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6955_ = crate::leanh::lean_box(0);
                v_a_6964_ = lean_array_uget_borrowed(v_as_6940_, v_i_6942_);
                if crate::leanh::lean_obj_tag(v_a_6964_) == 0 {
                    v_a_6957_ = v_snd_6951_;
                    state = 2;
                    continue;
                } else {
                    v_val_6965_ = crate::leanh::lean_ctor_get(v_a_6964_, 0);
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
                        if crate::leanh::lean_obj_tag(v___x_6968_) == 0 {
                            v_a_6969_ = crate::leanh::lean_ctor_get(v___x_6968_, 0);
                            crate::leanh::lean_inc(v_a_6969_);
                            crate::leanh::lean_dec_ref_known(v___x_6968_, 1);
                            v___x_6970_ = (crate::leanh::lean_unbox(v_a_6969_) as u8);
                            crate::leanh::lean_dec(v_a_6969_);
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
                            crate::leanh::lean_del_object(v___x_6953_);
                            crate::leanh::lean_dec(v_snd_6951_);
                            v_a_6973_ = crate::leanh::lean_ctor_get(v___x_6968_, 0);
                            v_isSharedCheck_6980_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6968_)) as u8;
                            if v_isSharedCheck_6980_ == 0 {
                                v___x_6975_ = v___x_6968_;
                                v_isShared_6976_ = v_isSharedCheck_6980_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6973_);
                                crate::leanh::lean_dec(v___x_6968_);
                                v___x_6975_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_6953_, 1, v_a_6957_);
                    crate::leanh::lean_ctor_set(v___x_6953_, 0, v___x_6955_);
                    v___x_6959_ = v___x_6953_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6963_, 0, v___x_6955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6963_, 1, v_a_6957_);
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
                    v_reuseFailAlloc_6979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6979_, 0, v_a_6973_);
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
    mut v_as_6983_: *mut crate::leanh::LeanObject,
    mut v_sz_6984_: *mut crate::leanh::LeanObject,
    mut v_i_6985_: *mut crate::leanh::LeanObject,
    mut v_b_6986_: *mut crate::leanh::LeanObject,
    mut v___y_6987_: *mut crate::leanh::LeanObject,
    mut v___y_6988_: *mut crate::leanh::LeanObject,
    mut v___y_6989_: *mut crate::leanh::LeanObject,
    mut v___y_6990_: *mut crate::leanh::LeanObject,
    mut v___y_6991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6992_: usize = 0;
    let mut v_i_boxed_6993_: usize = 0;
    let mut v_res_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6992_ = crate::leanh::lean_unbox_usize(v_sz_6984_);
    crate::leanh::lean_dec(v_sz_6984_);
    v_i_boxed_6993_ = crate::leanh::lean_unbox_usize(v_i_6985_);
    crate::leanh::lean_dec(v_i_6985_);
    v_res_6994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_6983_, v_sz_boxed_6992_, v_i_boxed_6993_, v_b_6986_, v___y_6987_, v___y_6988_, v___y_6989_, v___y_6990_);
    crate::leanh::lean_dec(v___y_6990_);
    crate::leanh::lean_dec_ref(v___y_6989_);
    crate::leanh::lean_dec(v___y_6988_);
    crate::leanh::lean_dec_ref(v___y_6987_);
    crate::leanh::lean_dec_ref(v_as_6983_);
    return v_res_6994_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(
    mut v_as_6995_: *mut crate::leanh::LeanObject,
    mut v_sz_6996_: usize,
    mut v_i_6997_: usize,
    mut v_b_6998_: *mut crate::leanh::LeanObject,
    mut v___y_6999_: *mut crate::leanh::LeanObject,
    mut v___y_7000_: *mut crate::leanh::LeanObject,
    mut v___y_7001_: *mut crate::leanh::LeanObject,
    mut v___y_7002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7004_: u8 = 0;
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7009_: u8 = 0;
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: usize = 0;
    let mut v___x_7016_: usize = 0;
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: u8 = 0;
    let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: u8 = 0;
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7031_: u8 = 0;
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7035_: u8 = 0;
    let mut v_isSharedCheck_7036_: u8 = 0;
    let mut v_unused_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7004_ = lean_usize_dec_lt(v_i_6997_, v_sz_6996_);
                if v___x_7004_ == 0 {
                    v___x_7005_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7005_, 0, v_b_6998_);
                    return v___x_7005_;
                } else {
                    v_snd_7006_ = crate::leanh::lean_ctor_get(v_b_6998_, 1);
                    v_isSharedCheck_7036_ = (!crate::leanh::lean_is_exclusive(v_b_6998_)) as u8;
                    if v_isSharedCheck_7036_ == 0 {
                        v_unused_7037_ = crate::leanh::lean_ctor_get(v_b_6998_, 0);
                        crate::leanh::lean_dec(v_unused_7037_);
                        v___x_7008_ = v_b_6998_;
                        v_isShared_7009_ = v_isSharedCheck_7036_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7006_);
                        crate::leanh::lean_dec(v_b_6998_);
                        v___x_7008_ = crate::leanh::lean_box(0);
                        v_isShared_7009_ = v_isSharedCheck_7036_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7010_ = crate::leanh::lean_box(0);
                v_a_7019_ = lean_array_uget_borrowed(v_as_6995_, v_i_6997_);
                if crate::leanh::lean_obj_tag(v_a_7019_) == 0 {
                    v_a_7012_ = v_snd_7006_;
                    state = 2;
                    continue;
                } else {
                    v_val_7020_ = crate::leanh::lean_ctor_get(v_a_7019_, 0);
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
                        if crate::leanh::lean_obj_tag(v___x_7023_) == 0 {
                            v_a_7024_ = crate::leanh::lean_ctor_get(v___x_7023_, 0);
                            crate::leanh::lean_inc(v_a_7024_);
                            crate::leanh::lean_dec_ref_known(v___x_7023_, 1);
                            v___x_7025_ = (crate::leanh::lean_unbox(v_a_7024_) as u8);
                            crate::leanh::lean_dec(v_a_7024_);
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
                            crate::leanh::lean_del_object(v___x_7008_);
                            crate::leanh::lean_dec(v_snd_7006_);
                            v_a_7028_ = crate::leanh::lean_ctor_get(v___x_7023_, 0);
                            v_isSharedCheck_7035_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7023_)) as u8;
                            if v_isSharedCheck_7035_ == 0 {
                                v___x_7030_ = v___x_7023_;
                                v_isShared_7031_ = v_isSharedCheck_7035_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7028_);
                                crate::leanh::lean_dec(v___x_7023_);
                                v___x_7030_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_7008_, 1, v_a_7012_);
                    crate::leanh::lean_ctor_set(v___x_7008_, 0, v___x_7010_);
                    v___x_7014_ = v___x_7008_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7018_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7018_, 0, v___x_7010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7018_, 1, v_a_7012_);
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
                    v_reuseFailAlloc_7034_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7034_, 0, v_a_7028_);
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
    mut v_as_7038_: *mut crate::leanh::LeanObject,
    mut v_sz_7039_: *mut crate::leanh::LeanObject,
    mut v_i_7040_: *mut crate::leanh::LeanObject,
    mut v_b_7041_: *mut crate::leanh::LeanObject,
    mut v___y_7042_: *mut crate::leanh::LeanObject,
    mut v___y_7043_: *mut crate::leanh::LeanObject,
    mut v___y_7044_: *mut crate::leanh::LeanObject,
    mut v___y_7045_: *mut crate::leanh::LeanObject,
    mut v___y_7046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7047_: usize = 0;
    let mut v_i_boxed_7048_: usize = 0;
    let mut v_res_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7047_ = crate::leanh::lean_unbox_usize(v_sz_7039_);
    crate::leanh::lean_dec(v_sz_7039_);
    v_i_boxed_7048_ = crate::leanh::lean_unbox_usize(v_i_7040_);
    crate::leanh::lean_dec(v_i_7040_);
    v_res_7049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_7038_, v_sz_boxed_7047_, v_i_boxed_7048_, v_b_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
    crate::leanh::lean_dec(v___y_7045_);
    crate::leanh::lean_dec_ref(v___y_7044_);
    crate::leanh::lean_dec(v___y_7043_);
    crate::leanh::lean_dec_ref(v___y_7042_);
    crate::leanh::lean_dec_ref(v_as_7038_);
    return v_res_7049_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(
    mut v_init_7050_: *mut crate::leanh::LeanObject,
    mut v_n_7051_: *mut crate::leanh::LeanObject,
    mut v_b_7052_: *mut crate::leanh::LeanObject,
    mut v___y_7053_: *mut crate::leanh::LeanObject,
    mut v___y_7054_: *mut crate::leanh::LeanObject,
    mut v___y_7055_: *mut crate::leanh::LeanObject,
    mut v___y_7056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7061_: usize = 0;
    let mut v___x_7062_: usize = 0;
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7067_: u8 = 0;
    let mut v_fst_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7078_: u8 = 0;
    let mut v_a_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7082_: u8 = 0;
    let mut v___x_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7086_: u8 = 0;
    let mut v_vs_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7090_: usize = 0;
    let mut v___x_7091_: usize = 0;
    let mut v___x_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7096_: u8 = 0;
    let mut v_fst_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7107_: u8 = 0;
    let mut v_a_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7111_: u8 = 0;
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_7051_) == 0 {
                    v_cs_7058_ = crate::leanh::lean_ctor_get(v_n_7051_, 0);
                    v___x_7059_ = crate::leanh::lean_box(0);
                    v___x_7060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7060_, 0, v___x_7059_);
                    crate::leanh::lean_ctor_set(v___x_7060_, 1, v_b_7052_);
                    v_sz_7061_ = lean_array_size(v_cs_7058_);
                    v___x_7062_ = 0usize;
                    v___x_7063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_7050_, v_cs_7058_, v_sz_7061_, v___x_7062_, v___x_7060_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
                    if crate::leanh::lean_obj_tag(v___x_7063_) == 0 {
                        v_a_7064_ = crate::leanh::lean_ctor_get(v___x_7063_, 0);
                        v_isSharedCheck_7078_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7063_)) as u8;
                        if v_isSharedCheck_7078_ == 0 {
                            v___x_7066_ = v___x_7063_;
                            v_isShared_7067_ = v_isSharedCheck_7078_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7064_);
                            crate::leanh::lean_dec(v___x_7063_);
                            v___x_7066_ = crate::leanh::lean_box(0);
                            v_isShared_7067_ = v_isSharedCheck_7078_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7079_ = crate::leanh::lean_ctor_get(v___x_7063_, 0);
                        v_isSharedCheck_7086_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7063_)) as u8;
                        if v_isSharedCheck_7086_ == 0 {
                            v___x_7081_ = v___x_7063_;
                            v_isShared_7082_ = v_isSharedCheck_7086_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7079_);
                            crate::leanh::lean_dec(v___x_7063_);
                            v___x_7081_ = crate::leanh::lean_box(0);
                            v_isShared_7082_ = v_isSharedCheck_7086_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_7087_ = crate::leanh::lean_ctor_get(v_n_7051_, 0);
                    v___x_7088_ = crate::leanh::lean_box(0);
                    v___x_7089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7089_, 0, v___x_7088_);
                    crate::leanh::lean_ctor_set(v___x_7089_, 1, v_b_7052_);
                    v_sz_7090_ = lean_array_size(v_vs_7087_);
                    v___x_7091_ = 0usize;
                    v___x_7092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_7087_, v_sz_7090_, v___x_7091_, v___x_7089_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
                    if crate::leanh::lean_obj_tag(v___x_7092_) == 0 {
                        v_a_7093_ = crate::leanh::lean_ctor_get(v___x_7092_, 0);
                        v_isSharedCheck_7107_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7092_)) as u8;
                        if v_isSharedCheck_7107_ == 0 {
                            v___x_7095_ = v___x_7092_;
                            v_isShared_7096_ = v_isSharedCheck_7107_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7093_);
                            crate::leanh::lean_dec(v___x_7092_);
                            v___x_7095_ = crate::leanh::lean_box(0);
                            v_isShared_7096_ = v_isSharedCheck_7107_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_7108_ = crate::leanh::lean_ctor_get(v___x_7092_, 0);
                        v_isSharedCheck_7115_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7092_)) as u8;
                        if v_isSharedCheck_7115_ == 0 {
                            v___x_7110_ = v___x_7092_;
                            v_isShared_7111_ = v_isSharedCheck_7115_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7108_);
                            crate::leanh::lean_dec(v___x_7092_);
                            v___x_7110_ = crate::leanh::lean_box(0);
                            v_isShared_7111_ = v_isSharedCheck_7115_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_7068_ = crate::leanh::lean_ctor_get(v_a_7064_, 0);
                if crate::leanh::lean_obj_tag(v_fst_7068_) == 0 {
                    v_snd_7069_ = crate::leanh::lean_ctor_get(v_a_7064_, 1);
                    crate::leanh::lean_inc(v_snd_7069_);
                    crate::leanh::lean_dec(v_a_7064_);
                    v___x_7070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7070_, 0, v_snd_7069_);
                    if v_isShared_7067_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7066_, 0, v___x_7070_);
                        v___x_7072_ = v___x_7066_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7073_, 0, v___x_7070_);
                        v___x_7072_ = v_reuseFailAlloc_7073_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_7068_);
                    crate::leanh::lean_dec(v_a_7064_);
                    v_val_7074_ = crate::leanh::lean_ctor_get(v_fst_7068_, 0);
                    crate::leanh::lean_inc(v_val_7074_);
                    crate::leanh::lean_dec_ref_known(v_fst_7068_, 1);
                    if v_isShared_7067_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7066_, 0, v_val_7074_);
                        v___x_7076_ = v___x_7066_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_val_7074_);
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
                    v_reuseFailAlloc_7085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7085_, 0, v_a_7079_);
                    v___x_7084_ = v_reuseFailAlloc_7085_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7084_;
            }
            6 => {
                v_fst_7097_ = crate::leanh::lean_ctor_get(v_a_7093_, 0);
                if crate::leanh::lean_obj_tag(v_fst_7097_) == 0 {
                    v_snd_7098_ = crate::leanh::lean_ctor_get(v_a_7093_, 1);
                    crate::leanh::lean_inc(v_snd_7098_);
                    crate::leanh::lean_dec(v_a_7093_);
                    v___x_7099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7099_, 0, v_snd_7098_);
                    if v_isShared_7096_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7095_, 0, v___x_7099_);
                        v___x_7101_ = v___x_7095_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7102_, 0, v___x_7099_);
                        v___x_7101_ = v_reuseFailAlloc_7102_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_7097_);
                    crate::leanh::lean_dec(v_a_7093_);
                    v_val_7103_ = crate::leanh::lean_ctor_get(v_fst_7097_, 0);
                    crate::leanh::lean_inc(v_val_7103_);
                    crate::leanh::lean_dec_ref_known(v_fst_7097_, 1);
                    if v_isShared_7096_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7095_, 0, v_val_7103_);
                        v___x_7105_ = v___x_7095_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7106_, 0, v_val_7103_);
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
                    v_reuseFailAlloc_7114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7114_, 0, v_a_7108_);
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
    mut v_init_7116_: *mut crate::leanh::LeanObject,
    mut v_as_7117_: *mut crate::leanh::LeanObject,
    mut v_sz_7118_: usize,
    mut v_i_7119_: usize,
    mut v_b_7120_: *mut crate::leanh::LeanObject,
    mut v___y_7121_: *mut crate::leanh::LeanObject,
    mut v___y_7122_: *mut crate::leanh::LeanObject,
    mut v___y_7123_: *mut crate::leanh::LeanObject,
    mut v___y_7124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7126_: u8 = 0;
    let mut v___x_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7131_: u8 = 0;
    let mut v_a_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7137_: u8 = 0;
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: usize = 0;
    let mut v___x_7150_: usize = 0;
    let mut v_reuseFailAlloc_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7153_: u8 = 0;
    let mut v_a_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7157_: u8 = 0;
    let mut v___x_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7161_: u8 = 0;
    let mut v_isSharedCheck_7162_: u8 = 0;
    let mut v_unused_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7126_ = lean_usize_dec_lt(v_i_7119_, v_sz_7118_);
                if v___x_7126_ == 0 {
                    v___x_7127_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7127_, 0, v_b_7120_);
                    return v___x_7127_;
                } else {
                    v_snd_7128_ = crate::leanh::lean_ctor_get(v_b_7120_, 1);
                    v_isSharedCheck_7162_ = (!crate::leanh::lean_is_exclusive(v_b_7120_)) as u8;
                    if v_isSharedCheck_7162_ == 0 {
                        v_unused_7163_ = crate::leanh::lean_ctor_get(v_b_7120_, 0);
                        crate::leanh::lean_dec(v_unused_7163_);
                        v___x_7130_ = v_b_7120_;
                        v_isShared_7131_ = v_isSharedCheck_7162_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7128_);
                        crate::leanh::lean_dec(v_b_7120_);
                        v___x_7130_ = crate::leanh::lean_box(0);
                        v_isShared_7131_ = v_isSharedCheck_7162_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_7132_ = lean_array_uget_borrowed(v_as_7117_, v_i_7119_);
                crate::leanh::lean_inc(v_snd_7128_);
                v___x_7133_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_7116_, v_a_7132_, v_snd_7128_, v___y_7121_, v___y_7122_, v___y_7123_, v___y_7124_);
                if crate::leanh::lean_obj_tag(v___x_7133_) == 0 {
                    v_a_7134_ = crate::leanh::lean_ctor_get(v___x_7133_, 0);
                    v_isSharedCheck_7153_ = (!crate::leanh::lean_is_exclusive(v___x_7133_)) as u8;
                    if v_isSharedCheck_7153_ == 0 {
                        v___x_7136_ = v___x_7133_;
                        v_isShared_7137_ = v_isSharedCheck_7153_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7134_);
                        crate::leanh::lean_dec(v___x_7133_);
                        v___x_7136_ = crate::leanh::lean_box(0);
                        v_isShared_7137_ = v_isSharedCheck_7153_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7130_);
                    crate::leanh::lean_dec(v_snd_7128_);
                    v_a_7154_ = crate::leanh::lean_ctor_get(v___x_7133_, 0);
                    v_isSharedCheck_7161_ = (!crate::leanh::lean_is_exclusive(v___x_7133_)) as u8;
                    if v_isSharedCheck_7161_ == 0 {
                        v___x_7156_ = v___x_7133_;
                        v_isShared_7157_ = v_isSharedCheck_7161_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7154_);
                        crate::leanh::lean_dec(v___x_7133_);
                        v___x_7156_ = crate::leanh::lean_box(0);
                        v_isShared_7157_ = v_isSharedCheck_7161_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_7134_) == 0 {
                    v___x_7138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7138_, 0, v_a_7134_);
                    if v_isShared_7131_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7130_, 0, v___x_7138_);
                        v___x_7140_ = v___x_7130_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7144_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7144_, 0, v___x_7138_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7144_, 1, v_snd_7128_);
                        v___x_7140_ = v_reuseFailAlloc_7144_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7136_);
                    crate::leanh::lean_dec(v_snd_7128_);
                    v_a_7145_ = crate::leanh::lean_ctor_get(v_a_7134_, 0);
                    crate::leanh::lean_inc(v_a_7145_);
                    crate::leanh::lean_dec_ref_known(v_a_7134_, 1);
                    v___x_7146_ = crate::leanh::lean_box(0);
                    if v_isShared_7131_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7130_, 1, v_a_7145_);
                        crate::leanh::lean_ctor_set(v___x_7130_, 0, v___x_7146_);
                        v___x_7148_ = v___x_7130_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7152_, 0, v___x_7146_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7152_, 1, v_a_7145_);
                        v___x_7148_ = v_reuseFailAlloc_7152_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7137_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7136_, 0, v___x_7140_);
                    v___x_7142_ = v___x_7136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7143_, 0, v___x_7140_);
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
                    v_reuseFailAlloc_7160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7160_, 0, v_a_7154_);
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
    mut v_init_7164_: *mut crate::leanh::LeanObject,
    mut v_as_7165_: *mut crate::leanh::LeanObject,
    mut v_sz_7166_: *mut crate::leanh::LeanObject,
    mut v_i_7167_: *mut crate::leanh::LeanObject,
    mut v_b_7168_: *mut crate::leanh::LeanObject,
    mut v___y_7169_: *mut crate::leanh::LeanObject,
    mut v___y_7170_: *mut crate::leanh::LeanObject,
    mut v___y_7171_: *mut crate::leanh::LeanObject,
    mut v___y_7172_: *mut crate::leanh::LeanObject,
    mut v___y_7173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7174_: usize = 0;
    let mut v_i_boxed_7175_: usize = 0;
    let mut v_res_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7174_ = crate::leanh::lean_unbox_usize(v_sz_7166_);
    crate::leanh::lean_dec(v_sz_7166_);
    v_i_boxed_7175_ = crate::leanh::lean_unbox_usize(v_i_7167_);
    crate::leanh::lean_dec(v_i_7167_);
    v_res_7176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_7164_, v_as_7165_, v_sz_boxed_7174_, v_i_boxed_7175_, v_b_7168_, v___y_7169_, v___y_7170_, v___y_7171_, v___y_7172_);
    crate::leanh::lean_dec(v___y_7172_);
    crate::leanh::lean_dec_ref(v___y_7171_);
    crate::leanh::lean_dec(v___y_7170_);
    crate::leanh::lean_dec_ref(v___y_7169_);
    crate::leanh::lean_dec_ref(v_as_7165_);
    crate::leanh::lean_dec_ref(v_init_7164_);
    return v_res_7176_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(
    mut v_init_7177_: *mut crate::leanh::LeanObject,
    mut v_n_7178_: *mut crate::leanh::LeanObject,
    mut v_b_7179_: *mut crate::leanh::LeanObject,
    mut v___y_7180_: *mut crate::leanh::LeanObject,
    mut v___y_7181_: *mut crate::leanh::LeanObject,
    mut v___y_7182_: *mut crate::leanh::LeanObject,
    mut v___y_7183_: *mut crate::leanh::LeanObject,
    mut v___y_7184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7185_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_7177_, v_n_7178_, v_b_7179_, v___y_7180_, v___y_7181_, v___y_7182_, v___y_7183_);
    crate::leanh::lean_dec(v___y_7183_);
    crate::leanh::lean_dec_ref(v___y_7182_);
    crate::leanh::lean_dec(v___y_7181_);
    crate::leanh::lean_dec_ref(v___y_7180_);
    crate::leanh::lean_dec_ref(v_n_7178_);
    crate::leanh::lean_dec_ref(v_init_7177_);
    return v_res_7185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(
    mut v_as_7186_: *mut crate::leanh::LeanObject,
    mut v_sz_7187_: usize,
    mut v_i_7188_: usize,
    mut v_b_7189_: *mut crate::leanh::LeanObject,
    mut v___y_7190_: *mut crate::leanh::LeanObject,
    mut v___y_7191_: *mut crate::leanh::LeanObject,
    mut v___y_7192_: *mut crate::leanh::LeanObject,
    mut v___y_7193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7195_: u8 = 0;
    let mut v___x_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7200_: u8 = 0;
    let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: usize = 0;
    let mut v___x_7207_: usize = 0;
    let mut v_reuseFailAlloc_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: u8 = 0;
    let mut v___x_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: u8 = 0;
    let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v___x_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7226_: u8 = 0;
    let mut v_isSharedCheck_7227_: u8 = 0;
    let mut v_unused_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7195_ = lean_usize_dec_lt(v_i_7188_, v_sz_7187_);
                if v___x_7195_ == 0 {
                    v___x_7196_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7196_, 0, v_b_7189_);
                    return v___x_7196_;
                } else {
                    v_snd_7197_ = crate::leanh::lean_ctor_get(v_b_7189_, 1);
                    v_isSharedCheck_7227_ = (!crate::leanh::lean_is_exclusive(v_b_7189_)) as u8;
                    if v_isSharedCheck_7227_ == 0 {
                        v_unused_7228_ = crate::leanh::lean_ctor_get(v_b_7189_, 0);
                        crate::leanh::lean_dec(v_unused_7228_);
                        v___x_7199_ = v_b_7189_;
                        v_isShared_7200_ = v_isSharedCheck_7227_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7197_);
                        crate::leanh::lean_dec(v_b_7189_);
                        v___x_7199_ = crate::leanh::lean_box(0);
                        v_isShared_7200_ = v_isSharedCheck_7227_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7201_ = crate::leanh::lean_box(0);
                v_a_7210_ = lean_array_uget_borrowed(v_as_7186_, v_i_7188_);
                if crate::leanh::lean_obj_tag(v_a_7210_) == 0 {
                    v_a_7203_ = v_snd_7197_;
                    state = 2;
                    continue;
                } else {
                    v_val_7211_ = crate::leanh::lean_ctor_get(v_a_7210_, 0);
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
                        if crate::leanh::lean_obj_tag(v___x_7214_) == 0 {
                            v_a_7215_ = crate::leanh::lean_ctor_get(v___x_7214_, 0);
                            crate::leanh::lean_inc(v_a_7215_);
                            crate::leanh::lean_dec_ref_known(v___x_7214_, 1);
                            v___x_7216_ = (crate::leanh::lean_unbox(v_a_7215_) as u8);
                            crate::leanh::lean_dec(v_a_7215_);
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
                            crate::leanh::lean_del_object(v___x_7199_);
                            crate::leanh::lean_dec(v_snd_7197_);
                            v_a_7219_ = crate::leanh::lean_ctor_get(v___x_7214_, 0);
                            v_isSharedCheck_7226_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7214_)) as u8;
                            if v_isSharedCheck_7226_ == 0 {
                                v___x_7221_ = v___x_7214_;
                                v_isShared_7222_ = v_isSharedCheck_7226_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7219_);
                                crate::leanh::lean_dec(v___x_7214_);
                                v___x_7221_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_7199_, 1, v_a_7203_);
                    crate::leanh::lean_ctor_set(v___x_7199_, 0, v___x_7201_);
                    v___x_7205_ = v___x_7199_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7209_, 0, v___x_7201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7209_, 1, v_a_7203_);
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
                    v_reuseFailAlloc_7225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7225_, 0, v_a_7219_);
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
    mut v_as_7229_: *mut crate::leanh::LeanObject,
    mut v_sz_7230_: *mut crate::leanh::LeanObject,
    mut v_i_7231_: *mut crate::leanh::LeanObject,
    mut v_b_7232_: *mut crate::leanh::LeanObject,
    mut v___y_7233_: *mut crate::leanh::LeanObject,
    mut v___y_7234_: *mut crate::leanh::LeanObject,
    mut v___y_7235_: *mut crate::leanh::LeanObject,
    mut v___y_7236_: *mut crate::leanh::LeanObject,
    mut v___y_7237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7238_: usize = 0;
    let mut v_i_boxed_7239_: usize = 0;
    let mut v_res_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7238_ = crate::leanh::lean_unbox_usize(v_sz_7230_);
    crate::leanh::lean_dec(v_sz_7230_);
    v_i_boxed_7239_ = crate::leanh::lean_unbox_usize(v_i_7231_);
    crate::leanh::lean_dec(v_i_7231_);
    v_res_7240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_7229_, v_sz_boxed_7238_, v_i_boxed_7239_, v_b_7232_, v___y_7233_, v___y_7234_, v___y_7235_, v___y_7236_);
    crate::leanh::lean_dec(v___y_7236_);
    crate::leanh::lean_dec_ref(v___y_7235_);
    crate::leanh::lean_dec(v___y_7234_);
    crate::leanh::lean_dec_ref(v___y_7233_);
    crate::leanh::lean_dec_ref(v_as_7229_);
    return v_res_7240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(
    mut v_as_7241_: *mut crate::leanh::LeanObject,
    mut v_sz_7242_: usize,
    mut v_i_7243_: usize,
    mut v_b_7244_: *mut crate::leanh::LeanObject,
    mut v___y_7245_: *mut crate::leanh::LeanObject,
    mut v___y_7246_: *mut crate::leanh::LeanObject,
    mut v___y_7247_: *mut crate::leanh::LeanObject,
    mut v___y_7248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7250_: u8 = 0;
    let mut v___x_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7255_: u8 = 0;
    let mut v___x_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: usize = 0;
    let mut v___x_7262_: usize = 0;
    let mut v___x_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: u8 = 0;
    let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: u8 = 0;
    let mut v___x_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7277_: u8 = 0;
    let mut v___x_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7281_: u8 = 0;
    let mut v_isSharedCheck_7282_: u8 = 0;
    let mut v_unused_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7250_ = lean_usize_dec_lt(v_i_7243_, v_sz_7242_);
                if v___x_7250_ == 0 {
                    v___x_7251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7251_, 0, v_b_7244_);
                    return v___x_7251_;
                } else {
                    v_snd_7252_ = crate::leanh::lean_ctor_get(v_b_7244_, 1);
                    v_isSharedCheck_7282_ = (!crate::leanh::lean_is_exclusive(v_b_7244_)) as u8;
                    if v_isSharedCheck_7282_ == 0 {
                        v_unused_7283_ = crate::leanh::lean_ctor_get(v_b_7244_, 0);
                        crate::leanh::lean_dec(v_unused_7283_);
                        v___x_7254_ = v_b_7244_;
                        v_isShared_7255_ = v_isSharedCheck_7282_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7252_);
                        crate::leanh::lean_dec(v_b_7244_);
                        v___x_7254_ = crate::leanh::lean_box(0);
                        v_isShared_7255_ = v_isSharedCheck_7282_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7256_ = crate::leanh::lean_box(0);
                v_a_7265_ = lean_array_uget_borrowed(v_as_7241_, v_i_7243_);
                if crate::leanh::lean_obj_tag(v_a_7265_) == 0 {
                    v_a_7258_ = v_snd_7252_;
                    state = 2;
                    continue;
                } else {
                    v_val_7266_ = crate::leanh::lean_ctor_get(v_a_7265_, 0);
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
                        if crate::leanh::lean_obj_tag(v___x_7269_) == 0 {
                            v_a_7270_ = crate::leanh::lean_ctor_get(v___x_7269_, 0);
                            crate::leanh::lean_inc(v_a_7270_);
                            crate::leanh::lean_dec_ref_known(v___x_7269_, 1);
                            v___x_7271_ = (crate::leanh::lean_unbox(v_a_7270_) as u8);
                            crate::leanh::lean_dec(v_a_7270_);
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
                            crate::leanh::lean_del_object(v___x_7254_);
                            crate::leanh::lean_dec(v_snd_7252_);
                            v_a_7274_ = crate::leanh::lean_ctor_get(v___x_7269_, 0);
                            v_isSharedCheck_7281_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7269_)) as u8;
                            if v_isSharedCheck_7281_ == 0 {
                                v___x_7276_ = v___x_7269_;
                                v_isShared_7277_ = v_isSharedCheck_7281_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7274_);
                                crate::leanh::lean_dec(v___x_7269_);
                                v___x_7276_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_7254_, 1, v_a_7258_);
                    crate::leanh::lean_ctor_set(v___x_7254_, 0, v___x_7256_);
                    v___x_7260_ = v___x_7254_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7264_, 0, v___x_7256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7264_, 1, v_a_7258_);
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
                    v_reuseFailAlloc_7280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7280_, 0, v_a_7274_);
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
    mut v_as_7284_: *mut crate::leanh::LeanObject,
    mut v_sz_7285_: *mut crate::leanh::LeanObject,
    mut v_i_7286_: *mut crate::leanh::LeanObject,
    mut v_b_7287_: *mut crate::leanh::LeanObject,
    mut v___y_7288_: *mut crate::leanh::LeanObject,
    mut v___y_7289_: *mut crate::leanh::LeanObject,
    mut v___y_7290_: *mut crate::leanh::LeanObject,
    mut v___y_7291_: *mut crate::leanh::LeanObject,
    mut v___y_7292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7293_: usize = 0;
    let mut v_i_boxed_7294_: usize = 0;
    let mut v_res_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7293_ = crate::leanh::lean_unbox_usize(v_sz_7285_);
    crate::leanh::lean_dec(v_sz_7285_);
    v_i_boxed_7294_ = crate::leanh::lean_unbox_usize(v_i_7286_);
    crate::leanh::lean_dec(v_i_7286_);
    v_res_7295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_7284_, v_sz_boxed_7293_, v_i_boxed_7294_, v_b_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_);
    crate::leanh::lean_dec(v___y_7291_);
    crate::leanh::lean_dec_ref(v___y_7290_);
    crate::leanh::lean_dec(v___y_7289_);
    crate::leanh::lean_dec_ref(v___y_7288_);
    crate::leanh::lean_dec_ref(v_as_7284_);
    return v_res_7295_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(
    mut v_t_7296_: *mut crate::leanh::LeanObject,
    mut v_init_7297_: *mut crate::leanh::LeanObject,
    mut v___y_7298_: *mut crate::leanh::LeanObject,
    mut v___y_7299_: *mut crate::leanh::LeanObject,
    mut v___y_7300_: *mut crate::leanh::LeanObject,
    mut v___y_7301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7309_: u8 = 0;
    let mut v_a_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7317_: usize = 0;
    let mut v___x_7318_: usize = 0;
    let mut v___x_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7323_: u8 = 0;
    let mut v_fst_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7333_: u8 = 0;
    let mut v_a_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7337_: u8 = 0;
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7341_: u8 = 0;
    let mut v_isSharedCheck_7342_: u8 = 0;
    let mut v_a_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7346_: u8 = 0;
    let mut v___x_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7303_ = crate::leanh::lean_ctor_get(v_t_7296_, 0);
                v_tail_7304_ = crate::leanh::lean_ctor_get(v_t_7296_, 1);
                crate::leanh::lean_inc_ref(v_init_7297_);
                v___x_7305_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_7297_, v_root_7303_, v_init_7297_, v___y_7298_, v___y_7299_, v___y_7300_, v___y_7301_);
                crate::leanh::lean_dec_ref(v_init_7297_);
                if crate::leanh::lean_obj_tag(v___x_7305_) == 0 {
                    v_a_7306_ = crate::leanh::lean_ctor_get(v___x_7305_, 0);
                    v_isSharedCheck_7342_ = (!crate::leanh::lean_is_exclusive(v___x_7305_)) as u8;
                    if v_isSharedCheck_7342_ == 0 {
                        v___x_7308_ = v___x_7305_;
                        v_isShared_7309_ = v_isSharedCheck_7342_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7306_);
                        crate::leanh::lean_dec(v___x_7305_);
                        v___x_7308_ = crate::leanh::lean_box(0);
                        v_isShared_7309_ = v_isSharedCheck_7342_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7343_ = crate::leanh::lean_ctor_get(v___x_7305_, 0);
                    v_isSharedCheck_7350_ = (!crate::leanh::lean_is_exclusive(v___x_7305_)) as u8;
                    if v_isSharedCheck_7350_ == 0 {
                        v___x_7345_ = v___x_7305_;
                        v_isShared_7346_ = v_isSharedCheck_7350_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7343_);
                        crate::leanh::lean_dec(v___x_7305_);
                        v___x_7345_ = crate::leanh::lean_box(0);
                        v_isShared_7346_ = v_isSharedCheck_7350_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7306_) == 0 {
                    v_a_7310_ = crate::leanh::lean_ctor_get(v_a_7306_, 0);
                    crate::leanh::lean_inc(v_a_7310_);
                    crate::leanh::lean_dec_ref_known(v_a_7306_, 1);
                    if v_isShared_7309_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7308_, 0, v_a_7310_);
                        v___x_7312_ = v___x_7308_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7313_, 0, v_a_7310_);
                        v___x_7312_ = v_reuseFailAlloc_7313_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7308_);
                    v_a_7314_ = crate::leanh::lean_ctor_get(v_a_7306_, 0);
                    crate::leanh::lean_inc(v_a_7314_);
                    crate::leanh::lean_dec_ref_known(v_a_7306_, 1);
                    v___x_7315_ = crate::leanh::lean_box(0);
                    v___x_7316_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7316_, 0, v___x_7315_);
                    crate::leanh::lean_ctor_set(v___x_7316_, 1, v_a_7314_);
                    v_sz_7317_ = lean_array_size(v_tail_7304_);
                    v___x_7318_ = 0usize;
                    v___x_7319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_7304_, v_sz_7317_, v___x_7318_, v___x_7316_, v___y_7298_, v___y_7299_, v___y_7300_, v___y_7301_);
                    if crate::leanh::lean_obj_tag(v___x_7319_) == 0 {
                        v_a_7320_ = crate::leanh::lean_ctor_get(v___x_7319_, 0);
                        v_isSharedCheck_7333_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7319_)) as u8;
                        if v_isSharedCheck_7333_ == 0 {
                            v___x_7322_ = v___x_7319_;
                            v_isShared_7323_ = v_isSharedCheck_7333_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7320_);
                            crate::leanh::lean_dec(v___x_7319_);
                            v___x_7322_ = crate::leanh::lean_box(0);
                            v_isShared_7323_ = v_isSharedCheck_7333_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7334_ = crate::leanh::lean_ctor_get(v___x_7319_, 0);
                        v_isSharedCheck_7341_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7319_)) as u8;
                        if v_isSharedCheck_7341_ == 0 {
                            v___x_7336_ = v___x_7319_;
                            v_isShared_7337_ = v_isSharedCheck_7341_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7334_);
                            crate::leanh::lean_dec(v___x_7319_);
                            v___x_7336_ = crate::leanh::lean_box(0);
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
                v_fst_7324_ = crate::leanh::lean_ctor_get(v_a_7320_, 0);
                if crate::leanh::lean_obj_tag(v_fst_7324_) == 0 {
                    v_snd_7325_ = crate::leanh::lean_ctor_get(v_a_7320_, 1);
                    crate::leanh::lean_inc(v_snd_7325_);
                    crate::leanh::lean_dec(v_a_7320_);
                    if v_isShared_7323_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7322_, 0, v_snd_7325_);
                        v___x_7327_ = v___x_7322_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7328_, 0, v_snd_7325_);
                        v___x_7327_ = v_reuseFailAlloc_7328_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_7324_);
                    crate::leanh::lean_dec(v_a_7320_);
                    v_val_7329_ = crate::leanh::lean_ctor_get(v_fst_7324_, 0);
                    crate::leanh::lean_inc(v_val_7329_);
                    crate::leanh::lean_dec_ref_known(v_fst_7324_, 1);
                    if v_isShared_7323_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7322_, 0, v_val_7329_);
                        v___x_7331_ = v___x_7322_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 0, v_val_7329_);
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
                    v_reuseFailAlloc_7340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7340_, 0, v_a_7334_);
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
                    v_reuseFailAlloc_7349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7349_, 0, v_a_7343_);
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
    mut v_t_7351_: *mut crate::leanh::LeanObject,
    mut v_init_7352_: *mut crate::leanh::LeanObject,
    mut v___y_7353_: *mut crate::leanh::LeanObject,
    mut v___y_7354_: *mut crate::leanh::LeanObject,
    mut v___y_7355_: *mut crate::leanh::LeanObject,
    mut v___y_7356_: *mut crate::leanh::LeanObject,
    mut v___y_7357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7358_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(
        v_t_7351_,
        v_init_7352_,
        v___y_7353_,
        v___y_7354_,
        v___y_7355_,
        v___y_7356_,
    );
    crate::leanh::lean_dec(v___y_7356_);
    crate::leanh::lean_dec_ref(v___y_7355_);
    crate::leanh::lean_dec(v___y_7354_);
    crate::leanh::lean_dec_ref(v___y_7353_);
    crate::leanh::lean_dec_ref(v_t_7351_);
    return v_res_7358_;
}
pub unsafe fn l_Lean_Meta_getPropHyps(
    mut v_a_7359_: *mut crate::leanh::LeanObject,
    mut v_a_7360_: *mut crate::leanh::LeanObject,
    mut v_a_7361_: *mut crate::leanh::LeanObject,
    mut v_a_7362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_7364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_7364_ = crate::leanh::lean_ctor_get(v_a_7359_, 2);
    v_decls_7365_ = crate::leanh::lean_ctor_get(v_lctx_7364_, 1);
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
    mut v_a_7368_: *mut crate::leanh::LeanObject,
    mut v_a_7369_: *mut crate::leanh::LeanObject,
    mut v_a_7370_: *mut crate::leanh::LeanObject,
    mut v_a_7371_: *mut crate::leanh::LeanObject,
    mut v_a_7372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7373_ = l_Lean_Meta_getPropHyps(v_a_7368_, v_a_7369_, v_a_7370_, v_a_7371_);
    crate::leanh::lean_dec(v_a_7371_);
    crate::leanh::lean_dec_ref(v_a_7370_);
    crate::leanh::lean_dec(v_a_7369_);
    crate::leanh::lean_dec_ref(v_a_7368_);
    return v_res_7373_;
}
pub unsafe fn _init_l_Lean_MVarId_inferInstance___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7377_ = l_Lean_MVarId_inferInstance___lam__0___closed__1;
    v___x_7378_ = l_Lean_MessageData_ofFormat(v___x_7377_);
    return v___x_7378_;
}
pub unsafe fn _init_l_Lean_MVarId_inferInstance___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7379_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_inferInstance___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_inferInstance___lam__0___closed__2_once),
        _init_l_Lean_MVarId_inferInstance___lam__0___closed__2,
    );
    v___x_7380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7380_, 0, v___x_7379_);
    return v___x_7380_;
}
pub unsafe fn l_Lean_MVarId_inferInstance___lam__0(
    mut v_mvarId_7381_: *mut crate::leanh::LeanObject,
    mut v___x_7382_: *mut crate::leanh::LeanObject,
    mut v___y_7383_: *mut crate::leanh::LeanObject,
    mut v___y_7384_: *mut crate::leanh::LeanObject,
    mut v___y_7385_: *mut crate::leanh::LeanObject,
    mut v___y_7386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7399_: u8 = 0;
    let mut v___x_7400_: u8 = 0;
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7407_: u8 = 0;
    let mut v_a_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7411_: u8 = 0;
    let mut v___x_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7415_: u8 = 0;
    let mut v_a_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7419_: u8 = 0;
    let mut v___x_7421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7423_: u8 = 0;
    let mut v_a_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7427_: u8 = 0;
    let mut v___x_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_7382_);
                crate::leanh::lean_inc(v_mvarId_7381_);
                v___x_7388_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_7381_,
                    v___x_7382_,
                    v___y_7383_,
                    v___y_7384_,
                    v___y_7385_,
                    v___y_7386_,
                );
                if crate::leanh::lean_obj_tag(v___x_7388_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7388_, 1);
                    crate::leanh::lean_inc(v_mvarId_7381_);
                    v___x_7389_ = l_Lean_MVarId_getType(
                        v_mvarId_7381_,
                        v___y_7383_,
                        v___y_7384_,
                        v___y_7385_,
                        v___y_7386_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7389_) == 0 {
                        v_a_7390_ = crate::leanh::lean_ctor_get(v___x_7389_, 0);
                        crate::leanh::lean_inc(v_a_7390_);
                        crate::leanh::lean_dec_ref_known(v___x_7389_, 1);
                        v___x_7391_ = crate::leanh::lean_box(0);
                        v___x_7392_ = l_Lean_Meta_synthInstance(
                            v_a_7390_,
                            v___x_7391_,
                            v___y_7383_,
                            v___y_7384_,
                            v___y_7385_,
                            v___y_7386_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7392_) == 0 {
                            v_a_7393_ = crate::leanh::lean_ctor_get(v___x_7392_, 0);
                            crate::leanh::lean_inc(v_a_7393_);
                            crate::leanh::lean_dec_ref_known(v___x_7392_, 1);
                            crate::leanh::lean_inc(v_mvarId_7381_);
                            v___x_7394_ = l_Lean_mkMVar(v_mvarId_7381_);
                            v___x_7395_ = l_Lean_Meta_isExprDefEq(
                                v___x_7394_,
                                v_a_7393_,
                                v___y_7383_,
                                v___y_7384_,
                                v___y_7385_,
                                v___y_7386_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7395_) == 0 {
                                v_a_7396_ = crate::leanh::lean_ctor_get(v___x_7395_, 0);
                                v_isSharedCheck_7407_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7395_)) as u8;
                                if v_isSharedCheck_7407_ == 0 {
                                    v___x_7398_ = v___x_7395_;
                                    v_isShared_7399_ = v_isSharedCheck_7407_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7396_);
                                    crate::leanh::lean_dec(v___x_7395_);
                                    v___x_7398_ = crate::leanh::lean_box(0);
                                    v_isShared_7399_ = v_isSharedCheck_7407_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_7382_);
                                crate::leanh::lean_dec(v_mvarId_7381_);
                                v_a_7408_ = crate::leanh::lean_ctor_get(v___x_7395_, 0);
                                v_isSharedCheck_7415_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7395_)) as u8;
                                if v_isSharedCheck_7415_ == 0 {
                                    v___x_7410_ = v___x_7395_;
                                    v_isShared_7411_ = v_isSharedCheck_7415_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7408_);
                                    crate::leanh::lean_dec(v___x_7395_);
                                    v___x_7410_ = crate::leanh::lean_box(0);
                                    v_isShared_7411_ = v_isSharedCheck_7415_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_7382_);
                            crate::leanh::lean_dec(v_mvarId_7381_);
                            v_a_7416_ = crate::leanh::lean_ctor_get(v___x_7392_, 0);
                            v_isSharedCheck_7423_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7392_)) as u8;
                            if v_isSharedCheck_7423_ == 0 {
                                v___x_7418_ = v___x_7392_;
                                v_isShared_7419_ = v_isSharedCheck_7423_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7416_);
                                crate::leanh::lean_dec(v___x_7392_);
                                v___x_7418_ = crate::leanh::lean_box(0);
                                v_isShared_7419_ = v_isSharedCheck_7423_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7382_);
                        crate::leanh::lean_dec(v_mvarId_7381_);
                        v_a_7424_ = crate::leanh::lean_ctor_get(v___x_7389_, 0);
                        v_isSharedCheck_7431_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7389_)) as u8;
                        if v_isSharedCheck_7431_ == 0 {
                            v___x_7426_ = v___x_7389_;
                            v_isShared_7427_ = v_isSharedCheck_7431_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7424_);
                            crate::leanh::lean_dec(v___x_7389_);
                            v___x_7426_ = crate::leanh::lean_box(0);
                            v_isShared_7427_ = v_isSharedCheck_7431_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7382_);
                    crate::leanh::lean_dec(v_mvarId_7381_);
                    return v___x_7388_;
                }
            }
            1 => {
                v___x_7400_ = (crate::leanh::lean_unbox(v_a_7396_) as u8);
                crate::leanh::lean_dec(v_a_7396_);
                if v___x_7400_ == 0 {
                    crate::leanh::lean_del_object(v___x_7398_);
                    v___x_7401_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v___x_7382_);
                    crate::leanh::lean_dec(v_mvarId_7381_);
                    v___x_7403_ = crate::leanh::lean_box(0);
                    if v_isShared_7399_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7398_, 0, v___x_7403_);
                        v___x_7405_ = v___x_7398_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7406_, 0, v___x_7403_);
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
                    v_reuseFailAlloc_7414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 0, v_a_7408_);
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
                    v_reuseFailAlloc_7422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7422_, 0, v_a_7416_);
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
                    v_reuseFailAlloc_7430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7430_, 0, v_a_7424_);
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
    mut v_mvarId_7432_: *mut crate::leanh::LeanObject,
    mut v___x_7433_: *mut crate::leanh::LeanObject,
    mut v___y_7434_: *mut crate::leanh::LeanObject,
    mut v___y_7435_: *mut crate::leanh::LeanObject,
    mut v___y_7436_: *mut crate::leanh::LeanObject,
    mut v___y_7437_: *mut crate::leanh::LeanObject,
    mut v___y_7438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7439_ = l_Lean_MVarId_inferInstance___lam__0(
        v_mvarId_7432_,
        v___x_7433_,
        v___y_7434_,
        v___y_7435_,
        v___y_7436_,
        v___y_7437_,
    );
    crate::leanh::lean_dec(v___y_7437_);
    crate::leanh::lean_dec_ref(v___y_7436_);
    crate::leanh::lean_dec(v___y_7435_);
    crate::leanh::lean_dec_ref(v___y_7434_);
    return v_res_7439_;
}
pub unsafe fn l_Lean_MVarId_inferInstance(
    mut v_mvarId_7443_: *mut crate::leanh::LeanObject,
    mut v_a_7444_: *mut crate::leanh::LeanObject,
    mut v_a_7445_: *mut crate::leanh::LeanObject,
    mut v_a_7446_: *mut crate::leanh::LeanObject,
    mut v_a_7447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7449_ = l_Lean_MVarId_inferInstance___closed__1;
    crate::leanh::lean_inc(v_mvarId_7443_);
    v___f_7450_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_inferInstance___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7450_, 0, v_mvarId_7443_);
    crate::leanh::lean_closure_set(v___f_7450_, 1, v___x_7449_);
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
    mut v_mvarId_7452_: *mut crate::leanh::LeanObject,
    mut v_a_7453_: *mut crate::leanh::LeanObject,
    mut v_a_7454_: *mut crate::leanh::LeanObject,
    mut v_a_7455_: *mut crate::leanh::LeanObject,
    mut v_a_7456_: *mut crate::leanh::LeanObject,
    mut v_a_7457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7458_ =
        l_Lean_MVarId_inferInstance(v_mvarId_7452_, v_a_7453_, v_a_7454_, v_a_7455_, v_a_7456_);
    crate::leanh::lean_dec(v_a_7456_);
    crate::leanh::lean_dec_ref(v_a_7455_);
    crate::leanh::lean_dec(v_a_7454_);
    crate::leanh::lean_dec_ref(v_a_7453_);
    return v_res_7458_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorIdx(
    mut v_x_7459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_7459_) {
        0 => {
            let mut v___x_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7460_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_7460_;
        }
        1 => {
            let mut v___x_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7461_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_7461_;
        }
        _ => {
            let mut v___x_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7462_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_7462_;
        }
    }
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(
    mut v_x_7463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7464_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_7463_);
    crate::leanh::lean_dec(v_x_7463_);
    return v_res_7464_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorElim___redArg(
    mut v_t_7465_: *mut crate::leanh::LeanObject,
    mut v_k_7466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_7465_) == 2 {
        let mut v_mvarId_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_7467_ = crate::leanh::lean_ctor_get(v_t_7465_, 0);
        crate::leanh::lean_inc(v_mvarId_7467_);
        crate::leanh::lean_dec_ref_known(v_t_7465_, 1);
        v___x_7468_ = crate::leanh::lean_apply_1(v_k_7466_, v_mvarId_7467_);
        return v___x_7468_;
    } else {
        crate::leanh::lean_dec(v_t_7465_);
        return v_k_7466_;
    }
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorElim(
    mut v_motive_7469_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_7470_: *mut crate::leanh::LeanObject,
    mut v_t_7471_: *mut crate::leanh::LeanObject,
    mut v_h_7472_: *mut crate::leanh::LeanObject,
    mut v_k_7473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7474_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7471_, v_k_7473_);
    return v___x_7474_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorElim___boxed(
    mut v_motive_7475_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_7476_: *mut crate::leanh::LeanObject,
    mut v_t_7477_: *mut crate::leanh::LeanObject,
    mut v_h_7478_: *mut crate::leanh::LeanObject,
    mut v_k_7479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7480_ = l_Lean_Meta_TacticResultCNM_ctorElim(
        v_motive_7475_,
        v_ctorIdx_7476_,
        v_t_7477_,
        v_h_7478_,
        v_k_7479_,
    );
    crate::leanh::lean_dec(v_ctorIdx_7476_);
    return v_res_7480_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_closed_elim___redArg(
    mut v_t_7481_: *mut crate::leanh::LeanObject,
    mut v_closed_7482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7483_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7481_, v_closed_7482_);
    return v___x_7483_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_closed_elim(
    mut v_motive_7484_: *mut crate::leanh::LeanObject,
    mut v_t_7485_: *mut crate::leanh::LeanObject,
    mut v_h_7486_: *mut crate::leanh::LeanObject,
    mut v_closed_7487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7488_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7485_, v_closed_7487_);
    return v___x_7488_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(
    mut v_t_7489_: *mut crate::leanh::LeanObject,
    mut v_noChange_7490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7491_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7489_, v_noChange_7490_);
    return v___x_7491_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_noChange_elim(
    mut v_motive_7492_: *mut crate::leanh::LeanObject,
    mut v_t_7493_: *mut crate::leanh::LeanObject,
    mut v_h_7494_: *mut crate::leanh::LeanObject,
    mut v_noChange_7495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7496_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7493_, v_noChange_7495_);
    return v___x_7496_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_modified_elim___redArg(
    mut v_t_7497_: *mut crate::leanh::LeanObject,
    mut v_modified_7498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7499_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7497_, v_modified_7498_);
    return v___x_7499_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_modified_elim(
    mut v_motive_7500_: *mut crate::leanh::LeanObject,
    mut v_t_7501_: *mut crate::leanh::LeanObject,
    mut v_h_7502_: *mut crate::leanh::LeanObject,
    mut v_modified_7503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7504_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7501_, v_modified_7503_);
    return v___x_7504_;
}
pub unsafe fn l_Lean_MVarId_isSubsingleton(
    mut v_g_7508_: *mut crate::leanh::LeanObject,
    mut v_a_7509_: *mut crate::leanh::LeanObject,
    mut v_a_7510_: *mut crate::leanh::LeanObject,
    mut v_a_7511_: *mut crate::leanh::LeanObject,
    mut v_a_7512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7516_: u8 = 0;
    let mut v___x_7517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: u8 = 0;
    let mut v___x_7523_: u8 = 0;
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7536_: u8 = 0;
    let mut v___x_7537_: u8 = 0;
    let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7542_: u8 = 0;
    let mut v_unused_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7524_ =
                    l_Lean_MVarId_getType(v_g_7508_, v_a_7509_, v_a_7510_, v_a_7511_, v_a_7512_);
                if crate::leanh::lean_obj_tag(v___x_7524_) == 0 {
                    v_a_7525_ = crate::leanh::lean_ctor_get(v___x_7524_, 0);
                    crate::leanh::lean_inc(v_a_7525_);
                    crate::leanh::lean_dec_ref_known(v___x_7524_, 1);
                    v___x_7526_ = l_Lean_MVarId_isSubsingleton___closed__1;
                    v___x_7527_ = crate::leanh::lean_unsigned_to_nat(1);
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
                    if crate::leanh::lean_obj_tag(v___x_7530_) == 0 {
                        v_a_7531_ = crate::leanh::lean_ctor_get(v___x_7530_, 0);
                        crate::leanh::lean_inc(v_a_7531_);
                        crate::leanh::lean_dec_ref_known(v___x_7530_, 1);
                        v___x_7532_ = crate::leanh::lean_box(0);
                        v___x_7533_ = l_Lean_Meta_synthInstance(
                            v_a_7531_,
                            v___x_7532_,
                            v_a_7509_,
                            v_a_7510_,
                            v_a_7511_,
                            v_a_7512_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7533_) == 0 {
                            v_isSharedCheck_7542_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7533_)) as u8;
                            if v_isSharedCheck_7542_ == 0 {
                                v_unused_7543_ = crate::leanh::lean_ctor_get(v___x_7533_, 0);
                                crate::leanh::lean_dec(v_unused_7543_);
                                v___x_7535_ = v___x_7533_;
                                v_isShared_7536_ = v_isSharedCheck_7542_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7533_);
                                v___x_7535_ = crate::leanh::lean_box(0);
                                v_isShared_7536_ = v_isSharedCheck_7542_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_7544_ = crate::leanh::lean_ctor_get(v___x_7533_, 0);
                            crate::leanh::lean_inc(v_a_7544_);
                            crate::leanh::lean_dec_ref_known(v___x_7533_, 1);
                            v_a_7521_ = v_a_7544_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_7545_ = crate::leanh::lean_ctor_get(v___x_7530_, 0);
                        crate::leanh::lean_inc(v_a_7545_);
                        crate::leanh::lean_dec_ref_known(v___x_7530_, 1);
                        v_a_7521_ = v_a_7545_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7546_ = crate::leanh::lean_ctor_get(v___x_7524_, 0);
                    crate::leanh::lean_inc(v_a_7546_);
                    crate::leanh::lean_dec_ref_known(v___x_7524_, 1);
                    v_a_7521_ = v_a_7546_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_7516_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_7515_);
                    v___x_7517_ = crate::leanh::lean_box((v___y_7516_) as usize);
                    v___x_7518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7518_, 0, v___x_7517_);
                    return v___x_7518_;
                } else {
                    v___x_7519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7519_, 0, v___y_7515_);
                    return v___x_7519_;
                }
            }
            2 => {
                v___x_7522_ = l_Lean_Exception_isInterrupt(v_a_7521_);
                if v___x_7522_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_7521_);
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
                v___x_7538_ = crate::leanh::lean_box((v___x_7537_) as usize);
                if v_isShared_7536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7535_, 0, v___x_7538_);
                    v___x_7540_ = v___x_7535_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7541_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7541_, 0, v___x_7538_);
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
    mut v_g_7547_: *mut crate::leanh::LeanObject,
    mut v_a_7548_: *mut crate::leanh::LeanObject,
    mut v_a_7549_: *mut crate::leanh::LeanObject,
    mut v_a_7550_: *mut crate::leanh::LeanObject,
    mut v_a_7551_: *mut crate::leanh::LeanObject,
    mut v_a_7552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7553_ =
        l_Lean_MVarId_isSubsingleton(v_g_7547_, v_a_7548_, v_a_7549_, v_a_7550_, v_a_7551_);
    crate::leanh::lean_dec(v_a_7551_);
    crate::leanh::lean_dec_ref(v_a_7550_);
    crate::leanh::lean_dec(v_a_7549_);
    crate::leanh::lean_dec_ref(v_a_7548_);
    return v_res_7553_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7571_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_;
    v___x_7572_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_;
    v___x_7573_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_;
    v___x_7574_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_7571_, v___x_7572_, v___x_7573_);
    return v___x_7574_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(
    mut v_a_7575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7576_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
    return v_res_7576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PPGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_debug_terminalTacticsAsSorry = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_debug_terminalTacticsAsSorry);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_tactic_skipAssignedInstances = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_tactic_skipAssignedInstances);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ForEachExprWhere(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_PPGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Util(builtin);
}
