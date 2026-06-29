// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Cbv
// Imports: Lean.Meta.Tactic.Cbv Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_getLhs___redArg,
    l_Lean_Elab_Tactic_Conv_updateLhs, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::Main::{
    l_Lean_Meta_Tactic_Cbv_cbv_warning, l_Lean_Meta_Tactic_Cbv_cbvEntry,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::{
    initialize_Lean_Meta_Tactic_Cbv, runtime_initialize_Lean_Meta_Tactic_Cbv,
};
use crate::lean_imports_rs::Init::Prelude::lean_string_dec_eq;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 97,
    m_capacity: 97,
    m_length: 96,
    m_data: [
        84, 104, 101, 32, 96, 99, 98, 118, 96, 32, 117, 115, 97, 103, 101, 32, 119, 97, 114, 110,
        105, 110, 103, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 101, 110, 97, 98, 108,
        101, 100, 46, 32, 68, 105, 115, 97, 98, 108, 101, 32, 105, 116, 32, 98, 121, 32, 115, 101,
        116, 116, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 99,
        98, 118, 46, 119, 97, 114, 110, 105, 110, 103, 32, 102, 97, 108, 115, 101, 96, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value) as *mut crate::leanh::LeanObject,2622230176999461939 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value) as *mut crate::leanh::LeanObject,12057338954073742905 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 118, 97, 108, 67, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value) as *mut crate::leanh::LeanObject,9299793053028177184 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value) as *mut crate::leanh::LeanObject,13629570598098759553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(
    mut v_opts_388_: *mut crate::leanh::LeanObject,
    mut v_opt_389_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_390_ = crate::leanh::lean_ctor_get(v_opt_389_, 0);
    v_defValue_391_ = crate::leanh::lean_ctor_get(v_opt_389_, 1);
    v_map_392_ = crate::leanh::lean_ctor_get(v_opts_388_, 0);
    v___x_393_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_392_,
            v_name_390_,
        );
    if crate::leanh::lean_obj_tag(v___x_393_) == 0 {
        let mut v___x_394_: u8 = 0;
        v___x_394_ = (crate::leanh::lean_unbox(v_defValue_391_) as u8);
        return v___x_394_;
    } else {
        let mut v_val_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_395_ = crate::leanh::lean_ctor_get(v___x_393_, 0);
        crate::leanh::lean_inc(v_val_395_);
        crate::leanh::lean_dec_ref_known(v___x_393_, 1);
        if crate::leanh::lean_obj_tag(v_val_395_) == 1 {
            let mut v_v_396_: u8 = 0;
            v_v_396_ = crate::leanh::lean_ctor_get_uint8(v_val_395_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_395_, 0);
            return v_v_396_;
        } else {
            let mut v___x_397_: u8 = 0;
            crate::leanh::lean_dec(v_val_395_);
            v___x_397_ = (crate::leanh::lean_unbox(v_defValue_391_) as u8);
            return v___x_397_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0___boxed(
    mut v_opts_398_: *mut crate::leanh::LeanObject,
    mut v_opt_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_400_: u8 = 0;
    let mut v_r_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ =
        l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v_opts_398_, v_opt_399_);
    crate::leanh::lean_dec_ref(v_opt_399_);
    crate::leanh::lean_dec_ref(v_opts_398_);
    v_r_401_ = crate::leanh::lean_box((v_res_400_) as usize);
    return v_r_401_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(
    mut v_msgData_402_: *mut crate::leanh::LeanObject,
    mut v___y_403_: *mut crate::leanh::LeanObject,
    mut v___y_404_: *mut crate::leanh::LeanObject,
    mut v___y_405_: *mut crate::leanh::LeanObject,
    mut v___y_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_408_ = lean_st_ref_get(v___y_406_);
    v_env_409_ = crate::leanh::lean_ctor_get(v___x_408_, 0);
    crate::leanh::lean_inc_ref(v_env_409_);
    crate::leanh::lean_dec(v___x_408_);
    v___x_410_ = lean_st_ref_get(v___y_404_);
    v_mctx_411_ = crate::leanh::lean_ctor_get(v___x_410_, 0);
    crate::leanh::lean_inc_ref(v_mctx_411_);
    crate::leanh::lean_dec(v___x_410_);
    v_lctx_412_ = crate::leanh::lean_ctor_get(v___y_403_, 2);
    v_options_413_ = crate::leanh::lean_ctor_get(v___y_405_, 2);
    crate::leanh::lean_inc_ref(v_options_413_);
    crate::leanh::lean_inc_ref(v_lctx_412_);
    v___x_414_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_414_, 0, v_env_409_);
    crate::leanh::lean_ctor_set(v___x_414_, 1, v_mctx_411_);
    crate::leanh::lean_ctor_set(v___x_414_, 2, v_lctx_412_);
    crate::leanh::lean_ctor_set(v___x_414_, 3, v_options_413_);
    v___x_415_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_415_, 0, v___x_414_);
    crate::leanh::lean_ctor_set(v___x_415_, 1, v_msgData_402_);
    v___x_416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_416_, 0, v___x_415_);
    return v___x_416_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_417_: *mut crate::leanh::LeanObject,
    mut v___y_418_: *mut crate::leanh::LeanObject,
    mut v___y_419_: *mut crate::leanh::LeanObject,
    mut v___y_420_: *mut crate::leanh::LeanObject,
    mut v___y_421_: *mut crate::leanh::LeanObject,
    mut v___y_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v_msgData_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
    crate::leanh::lean_dec(v___y_421_);
    crate::leanh::lean_dec_ref(v___y_420_);
    crate::leanh::lean_dec(v___y_419_);
    crate::leanh::lean_dec_ref(v___y_418_);
    return v_res_423_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(
    mut v___y_432_: u8,
    mut v_suppressElabErrors_433_: u8,
    mut v_x_434_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_434_) == 1 {
        let mut v_pre_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_435_ = crate::leanh::lean_ctor_get(v_x_434_, 0);
        match crate::leanh::lean_obj_tag(v_pre_435_) {
            1 => {
                let mut v_pre_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_436_ = crate::leanh::lean_ctor_get(v_pre_435_, 0);
                match crate::leanh::lean_obj_tag(v_pre_436_) {
                    0 => {
                        let mut v_str_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_440_: u8 = 0;
                        v_str_437_ = crate::leanh::lean_ctor_get(v_x_434_, 1);
                        v_str_438_ = crate::leanh::lean_ctor_get(v_pre_435_, 1);
                        v___x_439_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0;
                        v___x_440_ = lean_string_dec_eq(v_str_438_, v___x_439_);
                        if v___x_440_ == 0 {
                            let mut v___x_441_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_442_: u8 = 0;
                            v___x_441_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1;
                            v___x_442_ = lean_string_dec_eq(v_str_438_, v___x_441_);
                            if v___x_442_ == 0 {
                                return v___y_432_;
                            } else {
                                let mut v___x_443_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_444_: u8 = 0;
                                v___x_443_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2;
                                v___x_444_ = lean_string_dec_eq(v_str_437_, v___x_443_);
                                if v___x_444_ == 0 {
                                    return v___y_432_;
                                } else {
                                    return v_suppressElabErrors_433_;
                                }
                            }
                        } else {
                            let mut v___x_445_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_446_: u8 = 0;
                            v___x_445_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3;
                            v___x_446_ = lean_string_dec_eq(v_str_437_, v___x_445_);
                            if v___x_446_ == 0 {
                                return v___y_432_;
                            } else {
                                return v_suppressElabErrors_433_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_447_ = crate::leanh::lean_ctor_get(v_pre_436_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_447_) == 0 {
                            let mut v_str_448_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_449_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_450_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_451_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_452_: u8 = 0;
                            v_str_448_ = crate::leanh::lean_ctor_get(v_x_434_, 1);
                            v_str_449_ = crate::leanh::lean_ctor_get(v_pre_435_, 1);
                            v_str_450_ = crate::leanh::lean_ctor_get(v_pre_436_, 1);
                            v___x_451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4;
                            v___x_452_ = lean_string_dec_eq(v_str_450_, v___x_451_);
                            if v___x_452_ == 0 {
                                return v___y_432_;
                            } else {
                                let mut v___x_453_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_454_: u8 = 0;
                                v___x_453_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5;
                                v___x_454_ = lean_string_dec_eq(v_str_449_, v___x_453_);
                                if v___x_454_ == 0 {
                                    return v___y_432_;
                                } else {
                                    let mut v___x_455_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_456_: u8 = 0;
                                    v___x_455_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6;
                                    v___x_456_ = lean_string_dec_eq(v_str_448_, v___x_455_);
                                    if v___x_456_ == 0 {
                                        return v___y_432_;
                                    } else {
                                        return v_suppressElabErrors_433_;
                                    }
                                }
                            }
                        } else {
                            return v___y_432_;
                        }
                    }
                    _ => {
                        return v___y_432_;
                    }
                }
            }
            0 => {
                let mut v_str_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_459_: u8 = 0;
                v_str_457_ = crate::leanh::lean_ctor_get(v_x_434_, 1);
                v___x_458_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7;
                v___x_459_ = lean_string_dec_eq(v_str_457_, v___x_458_);
                if v___x_459_ == 0 {
                    return v___y_432_;
                } else {
                    return v_suppressElabErrors_433_;
                }
            }
            _ => {
                return v___y_432_;
            }
        }
    } else {
        return v___y_432_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(
    mut v___y_460_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_461_: *mut crate::leanh::LeanObject,
    mut v_x_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4772__boxed_463_: u8 = 0;
    let mut v_suppressElabErrors_boxed_464_: u8 = 0;
    let mut v_res_465_: u8 = 0;
    let mut v_r_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4772__boxed_463_ = (crate::leanh::lean_unbox(v___y_460_) as u8);
    v_suppressElabErrors_boxed_464_ = (crate::leanh::lean_unbox(v_suppressElabErrors_461_) as u8);
    v_res_465_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(v___y_4772__boxed_463_, v_suppressElabErrors_boxed_464_, v_x_462_);
    crate::leanh::lean_dec(v_x_462_);
    v_r_466_ = crate::leanh::lean_box((v_res_465_) as usize);
    return v_r_466_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(
    mut v_ref_468_: *mut crate::leanh::LeanObject,
    mut v_msgData_469_: *mut crate::leanh::LeanObject,
    mut v_severity_470_: u8,
    mut v_isSilent_471_: u8,
    mut v___y_472_: *mut crate::leanh::LeanObject,
    mut v___y_473_: *mut crate::leanh::LeanObject,
    mut v___y_474_: *mut crate::leanh::LeanObject,
    mut v___y_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_481_: u8 = 0;
    let mut v___y_482_: u8 = 0;
    let mut v___y_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_501_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut v___y_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_518_: u8 = 0;
    let mut v___y_519_: u8 = 0;
    let mut v___y_520_: u8 = 0;
    let mut v___y_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_527_: u8 = 0;
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: u8 = 0;
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_537_: u8 = 0;
    let mut v___y_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_543_: u8 = 0;
    let mut v___y_544_: u8 = 0;
    let mut v___y_545_: u8 = 0;
    let mut v___y_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_554_: u8 = 0;
    let mut v___y_555_: u8 = 0;
    let mut v___y_556_: u8 = 0;
    let mut v_ref_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: u8 = 0;
    let mut v___y_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_567_: u8 = 0;
    let mut v___y_568_: u8 = 0;
    let mut v___y_569_: u8 = 0;
    let mut v___y_571_: u8 = 0;
    let mut v_fileName_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_576_: u8 = 0;
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: u8 = 0;
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_561_ = 2;
                v___x_586_ = l_Lean_instBEqMessageSeverity_beq(v_severity_470_, v___x_561_);
                if v___x_586_ == 0 {
                    v___y_571_ = v___x_586_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_469_);
                    v___x_587_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_469_);
                    v___y_571_ = v___x_587_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_487_ = lean_st_ref_take(v___y_486_);
                v_currNamespace_488_ = crate::leanh::lean_ctor_get(v___y_485_, 6);
                v_openDecls_489_ = crate::leanh::lean_ctor_get(v___y_485_, 7);
                v_env_490_ = crate::leanh::lean_ctor_get(v___x_487_, 0);
                v_nextMacroScope_491_ = crate::leanh::lean_ctor_get(v___x_487_, 1);
                v_ngen_492_ = crate::leanh::lean_ctor_get(v___x_487_, 2);
                v_auxDeclNGen_493_ = crate::leanh::lean_ctor_get(v___x_487_, 3);
                v_traceState_494_ = crate::leanh::lean_ctor_get(v___x_487_, 4);
                v_cache_495_ = crate::leanh::lean_ctor_get(v___x_487_, 5);
                v_messages_496_ = crate::leanh::lean_ctor_get(v___x_487_, 6);
                v_infoState_497_ = crate::leanh::lean_ctor_get(v___x_487_, 7);
                v_snapshotTasks_498_ = crate::leanh::lean_ctor_get(v___x_487_, 8);
                v_isSharedCheck_512_ = (!crate::leanh::lean_is_exclusive(v___x_487_)) as u8;
                if v_isSharedCheck_512_ == 0 {
                    v___x_500_ = v___x_487_;
                    v_isShared_501_ = v_isSharedCheck_512_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_498_);
                    crate::leanh::lean_inc(v_infoState_497_);
                    crate::leanh::lean_inc(v_messages_496_);
                    crate::leanh::lean_inc(v_cache_495_);
                    crate::leanh::lean_inc(v_traceState_494_);
                    crate::leanh::lean_inc(v_auxDeclNGen_493_);
                    crate::leanh::lean_inc(v_ngen_492_);
                    crate::leanh::lean_inc(v_nextMacroScope_491_);
                    crate::leanh::lean_inc(v_env_490_);
                    crate::leanh::lean_dec(v___x_487_);
                    v___x_500_ = crate::leanh::lean_box(0);
                    v_isShared_501_ = v_isSharedCheck_512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_489_);
                crate::leanh::lean_inc(v_currNamespace_488_);
                v___x_502_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_502_, 0, v_currNamespace_488_);
                crate::leanh::lean_ctor_set(v___x_502_, 1, v_openDecls_489_);
                v___x_503_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_503_, 0, v___x_502_);
                crate::leanh::lean_ctor_set(v___x_503_, 1, v___y_480_);
                crate::leanh::lean_inc_ref(v___y_479_);
                crate::leanh::lean_inc_ref(v___y_478_);
                v___x_504_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_504_, 0, v___y_478_);
                crate::leanh::lean_ctor_set(v___x_504_, 1, v___y_484_);
                crate::leanh::lean_ctor_set(v___x_504_, 2, v___y_483_);
                crate::leanh::lean_ctor_set(v___x_504_, 3, v___y_479_);
                crate::leanh::lean_ctor_set(v___x_504_, 4, v___x_503_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_504_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_482_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_504_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_481_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_504_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_471_,
                );
                v___x_505_ = l_Lean_MessageLog_add(v___x_504_, v_messages_496_);
                if v_isShared_501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_500_, 6, v___x_505_);
                    v___x_507_ = v___x_500_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_511_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v_env_490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 1, v_nextMacroScope_491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 2, v_ngen_492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 3, v_auxDeclNGen_493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 4, v_traceState_494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 5, v_cache_495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 6, v___x_505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 7, v_infoState_497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 8, v_snapshotTasks_498_);
                    v___x_507_ = v_reuseFailAlloc_511_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_508_ = lean_st_ref_set(v___y_486_, v___x_507_);
                v___x_509_ = crate::leanh::lean_box(0);
                v___x_510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_510_, 0, v___x_509_);
                return v___x_510_;
            }
            4 => {
                v___x_522_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_469_,
                    );
                v___x_523_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v___x_522_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
                v_a_524_ = crate::leanh::lean_ctor_get(v___x_523_, 0);
                v_isSharedCheck_537_ = (!crate::leanh::lean_is_exclusive(v___x_523_)) as u8;
                if v_isSharedCheck_537_ == 0 {
                    v___x_526_ = v___x_523_;
                    v_isShared_527_ = v_isSharedCheck_537_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_524_);
                    crate::leanh::lean_dec(v___x_523_);
                    v___x_526_ = crate::leanh::lean_box(0);
                    v_isShared_527_ = v_isSharedCheck_537_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_516_, 2);
                v___x_528_ = l_Lean_FileMap_toPosition(v___y_516_, v___y_517_);
                crate::leanh::lean_dec(v___y_517_);
                v___x_529_ = l_Lean_FileMap_toPosition(v___y_516_, v___y_521_);
                crate::leanh::lean_dec(v___y_521_);
                v___x_530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_529_);
                v___x_531_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0;
                if v___y_520_ == 0 {
                    crate::leanh::lean_del_object(v___x_526_);
                    crate::leanh::lean_dec_ref(v___y_514_);
                    v___y_478_ = v___y_515_;
                    v___y_479_ = v___x_531_;
                    v___y_480_ = v_a_524_;
                    v___y_481_ = v___y_519_;
                    v___y_482_ = v___y_518_;
                    v___y_483_ = v___x_530_;
                    v___y_484_ = v___x_528_;
                    v___y_485_ = v___y_474_;
                    v___y_486_ = v___y_475_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_524_);
                    v___x_532_ = l_Lean_MessageData_hasTag(v___y_514_, v_a_524_);
                    if v___x_532_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_530_, 1);
                        crate::leanh::lean_dec_ref(v___x_528_);
                        crate::leanh::lean_dec(v_a_524_);
                        v___x_533_ = crate::leanh::lean_box(0);
                        if v_isShared_527_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_526_, 0, v___x_533_);
                            v___x_535_ = v___x_526_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
                            v___x_535_ = v_reuseFailAlloc_536_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_526_);
                        v___y_478_ = v___y_515_;
                        v___y_479_ = v___x_531_;
                        v___y_480_ = v_a_524_;
                        v___y_481_ = v___y_519_;
                        v___y_482_ = v___y_518_;
                        v___y_483_ = v___x_530_;
                        v___y_484_ = v___x_528_;
                        v___y_485_ = v___y_474_;
                        v___y_486_ = v___y_475_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_535_;
            }
            7 => {
                v___x_547_ = l_Lean_Syntax_getTailPos_x3f(v___y_542_, v___y_544_);
                crate::leanh::lean_dec(v___y_542_);
                if crate::leanh::lean_obj_tag(v___x_547_) == 0 {
                    crate::leanh::lean_inc(v___y_546_);
                    v___y_514_ = v___y_539_;
                    v___y_515_ = v___y_540_;
                    v___y_516_ = v___y_541_;
                    v___y_517_ = v___y_546_;
                    v___y_518_ = v___y_544_;
                    v___y_519_ = v___y_543_;
                    v___y_520_ = v___y_545_;
                    v___y_521_ = v___y_546_;
                    state = 4;
                    continue;
                } else {
                    v_val_548_ = crate::leanh::lean_ctor_get(v___x_547_, 0);
                    crate::leanh::lean_inc(v_val_548_);
                    crate::leanh::lean_dec_ref_known(v___x_547_, 1);
                    v___y_514_ = v___y_539_;
                    v___y_515_ = v___y_540_;
                    v___y_516_ = v___y_541_;
                    v___y_517_ = v___y_546_;
                    v___y_518_ = v___y_544_;
                    v___y_519_ = v___y_543_;
                    v___y_520_ = v___y_545_;
                    v___y_521_ = v_val_548_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_557_ = l_Lean_replaceRef(v_ref_468_, v___y_552_);
                v___x_558_ = l_Lean_Syntax_getPos_x3f(v_ref_557_, v___y_554_);
                if crate::leanh::lean_obj_tag(v___x_558_) == 0 {
                    v___x_559_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_539_ = v___y_550_;
                    v___y_540_ = v___y_551_;
                    v___y_541_ = v___y_553_;
                    v___y_542_ = v_ref_557_;
                    v___y_543_ = v___y_556_;
                    v___y_544_ = v___y_554_;
                    v___y_545_ = v___y_555_;
                    v___y_546_ = v___x_559_;
                    state = 7;
                    continue;
                } else {
                    v_val_560_ = crate::leanh::lean_ctor_get(v___x_558_, 0);
                    crate::leanh::lean_inc(v_val_560_);
                    crate::leanh::lean_dec_ref_known(v___x_558_, 1);
                    v___y_539_ = v___y_550_;
                    v___y_540_ = v___y_551_;
                    v___y_541_ = v___y_553_;
                    v___y_542_ = v_ref_557_;
                    v___y_543_ = v___y_556_;
                    v___y_544_ = v___y_554_;
                    v___y_545_ = v___y_555_;
                    v___y_546_ = v_val_560_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_569_ == 0 {
                    v___y_550_ = v___y_566_;
                    v___y_551_ = v___y_563_;
                    v___y_552_ = v___y_564_;
                    v___y_553_ = v___y_565_;
                    v___y_554_ = v___y_568_;
                    v___y_555_ = v___y_567_;
                    v___y_556_ = v_severity_470_;
                    state = 8;
                    continue;
                } else {
                    v___y_550_ = v___y_566_;
                    v___y_551_ = v___y_563_;
                    v___y_552_ = v___y_564_;
                    v___y_553_ = v___y_565_;
                    v___y_554_ = v___y_568_;
                    v___y_555_ = v___y_567_;
                    v___y_556_ = v___x_561_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_571_ == 0 {
                    v_fileName_572_ = crate::leanh::lean_ctor_get(v___y_474_, 0);
                    v_fileMap_573_ = crate::leanh::lean_ctor_get(v___y_474_, 1);
                    v_options_574_ = crate::leanh::lean_ctor_get(v___y_474_, 2);
                    v_ref_575_ = crate::leanh::lean_ctor_get(v___y_474_, 5);
                    v_suppressElabErrors_576_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_474_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_577_ = crate::leanh::lean_box((v___y_571_) as usize);
                    v___x_578_ = crate::leanh::lean_box((v_suppressElabErrors_576_) as usize);
                    v___f_579_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_579_, 0, v___x_577_);
                    crate::leanh::lean_closure_set(v___f_579_, 1, v___x_578_);
                    v___x_580_ = 1;
                    v___x_581_ = l_Lean_instBEqMessageSeverity_beq(v_severity_470_, v___x_580_);
                    if v___x_581_ == 0 {
                        v___y_563_ = v_fileName_572_;
                        v___y_564_ = v_ref_575_;
                        v___y_565_ = v_fileMap_573_;
                        v___y_566_ = v___f_579_;
                        v___y_567_ = v_suppressElabErrors_576_;
                        v___y_568_ = v___y_571_;
                        v___y_569_ = v___x_581_;
                        state = 9;
                        continue;
                    } else {
                        v___x_582_ = l_Lean_warningAsError;
                        v___x_583_ =
                            l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(
                                v_options_574_,
                                v___x_582_,
                            );
                        v___y_563_ = v_fileName_572_;
                        v___y_564_ = v_ref_575_;
                        v___y_565_ = v_fileMap_573_;
                        v___y_566_ = v___f_579_;
                        v___y_567_ = v_suppressElabErrors_576_;
                        v___y_568_ = v___y_571_;
                        v___y_569_ = v___x_583_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_469_);
                    v___x_584_ = crate::leanh::lean_box(0);
                    v___x_585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_585_, 0, v___x_584_);
                    return v___x_585_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___boxed(
    mut v_ref_588_: *mut crate::leanh::LeanObject,
    mut v_msgData_589_: *mut crate::leanh::LeanObject,
    mut v_severity_590_: *mut crate::leanh::LeanObject,
    mut v_isSilent_591_: *mut crate::leanh::LeanObject,
    mut v___y_592_: *mut crate::leanh::LeanObject,
    mut v___y_593_: *mut crate::leanh::LeanObject,
    mut v___y_594_: *mut crate::leanh::LeanObject,
    mut v___y_595_: *mut crate::leanh::LeanObject,
    mut v___y_596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_597_: u8 = 0;
    let mut v_isSilent_boxed_598_: u8 = 0;
    let mut v_res_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_597_ = (crate::leanh::lean_unbox(v_severity_590_) as u8);
    v_isSilent_boxed_598_ = (crate::leanh::lean_unbox(v_isSilent_591_) as u8);
    v_res_599_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_588_, v_msgData_589_, v_severity_boxed_597_, v_isSilent_boxed_598_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
    crate::leanh::lean_dec(v___y_595_);
    crate::leanh::lean_dec_ref(v___y_594_);
    crate::leanh::lean_dec(v___y_593_);
    crate::leanh::lean_dec_ref(v___y_592_);
    crate::leanh::lean_dec(v_ref_588_);
    return v_res_599_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(
    mut v_ref_600_: *mut crate::leanh::LeanObject,
    mut v_msgData_601_: *mut crate::leanh::LeanObject,
    mut v___y_602_: *mut crate::leanh::LeanObject,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
    mut v___y_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_611_: u8 = 0;
    let mut v___x_612_: u8 = 0;
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_611_ = 1;
    v___x_612_ = 0;
    v___x_613_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_600_, v_msgData_601_, v___x_611_, v___x_612_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
    return v___x_613_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1___boxed(
    mut v_ref_614_: *mut crate::leanh::LeanObject,
    mut v_msgData_615_: *mut crate::leanh::LeanObject,
    mut v___y_616_: *mut crate::leanh::LeanObject,
    mut v___y_617_: *mut crate::leanh::LeanObject,
    mut v___y_618_: *mut crate::leanh::LeanObject,
    mut v___y_619_: *mut crate::leanh::LeanObject,
    mut v___y_620_: *mut crate::leanh::LeanObject,
    mut v___y_621_: *mut crate::leanh::LeanObject,
    mut v___y_622_: *mut crate::leanh::LeanObject,
    mut v___y_623_: *mut crate::leanh::LeanObject,
    mut v___y_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_625_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(
        v_ref_614_,
        v_msgData_615_,
        v___y_616_,
        v___y_617_,
        v___y_618_,
        v___y_619_,
        v___y_620_,
        v___y_621_,
        v___y_622_,
        v___y_623_,
    );
    crate::leanh::lean_dec(v___y_623_);
    crate::leanh::lean_dec_ref(v___y_622_);
    crate::leanh::lean_dec(v___y_621_);
    crate::leanh::lean_dec_ref(v___y_620_);
    crate::leanh::lean_dec(v___y_619_);
    crate::leanh::lean_dec_ref(v___y_618_);
    crate::leanh::lean_dec(v___y_617_);
    crate::leanh::lean_dec_ref(v___y_616_);
    crate::leanh::lean_dec(v_ref_614_);
    return v_res_625_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1;
    v___x_630_ = l_Lean_MessageData_ofFormat(v___x_629_);
    return v___x_630_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(
    mut v_stx_631_: *mut crate::leanh::LeanObject,
    mut v___y_632_: *mut crate::leanh::LeanObject,
    mut v___y_633_: *mut crate::leanh::LeanObject,
    mut v___y_634_: *mut crate::leanh::LeanObject,
    mut v___y_635_: *mut crate::leanh::LeanObject,
    mut v___y_636_: *mut crate::leanh::LeanObject,
    mut v___y_637_: *mut crate::leanh::LeanObject,
    mut v___y_638_: *mut crate::leanh::LeanObject,
    mut v___y_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut v_a_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_668_: u8 = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_672_: u8 = 0;
    let mut v_a_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_676_: u8 = 0;
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_680_: u8 = 0;
    let mut v_options_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_681_ = crate::leanh::lean_ctor_get(v___y_638_, 2);
                v___x_682_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
                v___x_683_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(
                    v_options_681_,
                    v___x_682_,
                );
                if v___x_683_ == 0 {
                    v___y_642_ = v___y_632_;
                    v___y_643_ = v___y_633_;
                    v___y_644_ = v___y_634_;
                    v___y_645_ = v___y_635_;
                    v___y_646_ = v___y_636_;
                    v___y_647_ = v___y_637_;
                    v___y_648_ = v___y_638_;
                    v___y_649_ = v___y_639_;
                    state = 1;
                    continue;
                } else {
                    v___x_684_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2,
                    );
                    v___x_685_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(
                        v_stx_631_, v___x_684_, v___y_632_, v___y_633_, v___y_634_, v___y_635_,
                        v___y_636_, v___y_637_, v___y_638_, v___y_639_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_685_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_685_, 1);
                        v___y_642_ = v___y_632_;
                        v___y_643_ = v___y_633_;
                        v___y_644_ = v___y_634_;
                        v___y_645_ = v___y_635_;
                        v___y_646_ = v___y_636_;
                        v___y_647_ = v___y_637_;
                        v___y_648_ = v___y_638_;
                        v___y_649_ = v___y_639_;
                        state = 1;
                        continue;
                    } else {
                        return v___x_685_;
                    }
                }
            }
            1 => {
                v___x_650_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_643_, v___y_646_, v___y_647_, v___y_648_, v___y_649_,
                );
                if crate::leanh::lean_obj_tag(v___x_650_) == 0 {
                    v_a_651_ = crate::leanh::lean_ctor_get(v___x_650_, 0);
                    crate::leanh::lean_inc(v_a_651_);
                    crate::leanh::lean_dec_ref_known(v___x_650_, 1);
                    v___x_652_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(
                        v_a_651_, v___y_646_, v___y_647_, v___y_648_, v___y_649_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_652_) == 0 {
                        v_a_653_ = crate::leanh::lean_ctor_get(v___x_652_, 0);
                        v_isSharedCheck_664_ = (!crate::leanh::lean_is_exclusive(v___x_652_)) as u8;
                        if v_isSharedCheck_664_ == 0 {
                            v___x_655_ = v___x_652_;
                            v_isShared_656_ = v_isSharedCheck_664_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_653_);
                            crate::leanh::lean_dec(v___x_652_);
                            v___x_655_ = crate::leanh::lean_box(0);
                            v_isShared_656_ = v_isSharedCheck_664_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_665_ = crate::leanh::lean_ctor_get(v___x_652_, 0);
                        v_isSharedCheck_672_ = (!crate::leanh::lean_is_exclusive(v___x_652_)) as u8;
                        if v_isSharedCheck_672_ == 0 {
                            v___x_667_ = v___x_652_;
                            v_isShared_668_ = v_isSharedCheck_672_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_665_);
                            crate::leanh::lean_dec(v___x_652_);
                            v___x_667_ = crate::leanh::lean_box(0);
                            v_isShared_668_ = v_isSharedCheck_672_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_673_ = crate::leanh::lean_ctor_get(v___x_650_, 0);
                    v_isSharedCheck_680_ = (!crate::leanh::lean_is_exclusive(v___x_650_)) as u8;
                    if v_isSharedCheck_680_ == 0 {
                        v___x_675_ = v___x_650_;
                        v_isShared_676_ = v_isSharedCheck_680_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_673_);
                        crate::leanh::lean_dec(v___x_650_);
                        v___x_675_ = crate::leanh::lean_box(0);
                        v_isShared_676_ = v_isSharedCheck_680_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_653_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_653_, 0);
                    v___x_657_ = crate::leanh::lean_box(0);
                    if v_isShared_656_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_655_, 0, v___x_657_);
                        v___x_659_ = v___x_655_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
                        v___x_659_ = v_reuseFailAlloc_660_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_655_);
                    v_e_x27_661_ = crate::leanh::lean_ctor_get(v_a_653_, 0);
                    crate::leanh::lean_inc_ref(v_e_x27_661_);
                    v_proof_662_ = crate::leanh::lean_ctor_get(v_a_653_, 1);
                    crate::leanh::lean_inc_ref(v_proof_662_);
                    crate::leanh::lean_dec_ref_known(v_a_653_, 2);
                    v___x_663_ = l_Lean_Elab_Tactic_Conv_updateLhs(
                        v_e_x27_661_,
                        v_proof_662_,
                        v___y_642_,
                        v___y_643_,
                        v___y_644_,
                        v___y_645_,
                        v___y_646_,
                        v___y_647_,
                        v___y_648_,
                        v___y_649_,
                    );
                    return v___x_663_;
                }
            }
            3 => {
                return v___x_659_;
            }
            4 => {
                if v_isShared_668_ == 0 {
                    v___x_670_ = v___x_667_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
                    v___x_670_ = v_reuseFailAlloc_671_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_670_;
            }
            6 => {
                if v_isShared_676_ == 0 {
                    v___x_678_ = v___x_675_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
                    v___x_678_ = v_reuseFailAlloc_679_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed(
    mut v_stx_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
    mut v___y_688_: *mut crate::leanh::LeanObject,
    mut v___y_689_: *mut crate::leanh::LeanObject,
    mut v___y_690_: *mut crate::leanh::LeanObject,
    mut v___y_691_: *mut crate::leanh::LeanObject,
    mut v___y_692_: *mut crate::leanh::LeanObject,
    mut v___y_693_: *mut crate::leanh::LeanObject,
    mut v___y_694_: *mut crate::leanh::LeanObject,
    mut v___y_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(
        v_stx_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_,
        v___y_693_, v___y_694_,
    );
    crate::leanh::lean_dec(v___y_694_);
    crate::leanh::lean_dec_ref(v___y_693_);
    crate::leanh::lean_dec(v___y_692_);
    crate::leanh::lean_dec_ref(v___y_691_);
    crate::leanh::lean_dec(v___y_690_);
    crate::leanh::lean_dec_ref(v___y_689_);
    crate::leanh::lean_dec(v___y_688_);
    crate::leanh::lean_dec_ref(v___y_687_);
    crate::leanh::lean_dec(v_stx_686_);
    return v_res_696_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv(
    mut v_stx_697_: *mut crate::leanh::LeanObject,
    mut v_a_698_: *mut crate::leanh::LeanObject,
    mut v_a_699_: *mut crate::leanh::LeanObject,
    mut v_a_700_: *mut crate::leanh::LeanObject,
    mut v_a_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
    mut v_a_705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_707_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    crate::leanh::lean_closure_set(v___f_707_, 0, v_stx_697_);
    v___x_708_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_707_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_,
    );
    return v___x_708_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv___boxed(
    mut v_stx_709_: *mut crate::leanh::LeanObject,
    mut v_a_710_: *mut crate::leanh::LeanObject,
    mut v_a_711_: *mut crate::leanh::LeanObject,
    mut v_a_712_: *mut crate::leanh::LeanObject,
    mut v_a_713_: *mut crate::leanh::LeanObject,
    mut v_a_714_: *mut crate::leanh::LeanObject,
    mut v_a_715_: *mut crate::leanh::LeanObject,
    mut v_a_716_: *mut crate::leanh::LeanObject,
    mut v_a_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_719_ = l_Lean_Elab_Tactic_Conv_evalCbv(
        v_stx_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_,
    );
    crate::leanh::lean_dec(v_a_717_);
    crate::leanh::lean_dec_ref(v_a_716_);
    crate::leanh::lean_dec(v_a_715_);
    crate::leanh::lean_dec_ref(v_a_714_);
    crate::leanh::lean_dec(v_a_713_);
    crate::leanh::lean_dec_ref(v_a_712_);
    crate::leanh::lean_dec(v_a_711_);
    crate::leanh::lean_dec_ref(v_a_710_);
    return v_res_719_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(
    mut v_ref_720_: *mut crate::leanh::LeanObject,
    mut v_msgData_721_: *mut crate::leanh::LeanObject,
    mut v_severity_722_: u8,
    mut v_isSilent_723_: u8,
    mut v___y_724_: *mut crate::leanh::LeanObject,
    mut v___y_725_: *mut crate::leanh::LeanObject,
    mut v___y_726_: *mut crate::leanh::LeanObject,
    mut v___y_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
    mut v___y_729_: *mut crate::leanh::LeanObject,
    mut v___y_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_720_, v_msgData_721_, v_severity_722_, v_isSilent_723_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
    return v___x_733_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___boxed(
    mut v_ref_734_: *mut crate::leanh::LeanObject,
    mut v_msgData_735_: *mut crate::leanh::LeanObject,
    mut v_severity_736_: *mut crate::leanh::LeanObject,
    mut v_isSilent_737_: *mut crate::leanh::LeanObject,
    mut v___y_738_: *mut crate::leanh::LeanObject,
    mut v___y_739_: *mut crate::leanh::LeanObject,
    mut v___y_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_747_: u8 = 0;
    let mut v_isSilent_boxed_748_: u8 = 0;
    let mut v_res_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_747_ = (crate::leanh::lean_unbox(v_severity_736_) as u8);
    v_isSilent_boxed_748_ = (crate::leanh::lean_unbox(v_isSilent_737_) as u8);
    v_res_749_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(v_ref_734_, v_msgData_735_, v_severity_boxed_747_, v_isSilent_boxed_748_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
    crate::leanh::lean_dec(v___y_745_);
    crate::leanh::lean_dec_ref(v___y_744_);
    crate::leanh::lean_dec(v___y_743_);
    crate::leanh::lean_dec_ref(v___y_742_);
    crate::leanh::lean_dec(v___y_741_);
    crate::leanh::lean_dec_ref(v___y_740_);
    crate::leanh::lean_dec(v___y_739_);
    crate::leanh::lean_dec_ref(v___y_738_);
    crate::leanh::lean_dec(v_ref_734_);
    return v_res_749_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_769_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4;
    v___x_770_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6;
    v___x_771_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalCbv___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_772_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_768_, v___x_769_, v___x_770_, v___x_771_,
    );
    return v___x_772_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___boxed(
    mut v_a_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
    return v_res_774_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Cbv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Cbv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Cbv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Cbv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
}
