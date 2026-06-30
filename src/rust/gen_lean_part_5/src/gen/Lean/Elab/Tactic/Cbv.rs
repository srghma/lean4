// Lean compiler output
// Module: Lean.Elab.Tactic.Cbv
// Imports: Lean.Meta.Tactic.Cbv Lean.Meta.Tactic Lean.Elab.Tactic.Location
use crate::ffi::{lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_getFVarIds;
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::l_Lean_MVarId_applyConst;
use crate::r#gen::Lean::Meta::Tactic::Cbv::Main::{
    l_Lean_Meta_Tactic_Cbv_cbv_warning, l_Lean_Meta_Tactic_Cbv_cbvDecideGoal,
    l_Lean_Meta_Tactic_Cbv_cbvGoal,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::{
    initialize_Lean_Meta_Tactic_Cbv, runtime_initialize_Lean_Meta_Tactic_Cbv,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getNondepPropHyps;
use crate::r#gen::Lean::Meta::Tactic::{
    initialize_Lean_Meta_Tactic, runtime_initialize_Lean_Meta_Tactic,
};
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0_value:
    leanh::LeanStringObject<97> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value) as *mut leanh::LeanObject,14040092659935610240 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 118, 97, 108, 67, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value) as *mut leanh::LeanObject,11560057156626128935 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value) as *mut leanh::LeanObject,552649593872933314 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 97, 112, 112, 108, 121, 32, 96, 111, 102,
        95, 100, 101, 99, 105, 100, 101, 95, 101, 113, 95, 116, 114, 117, 101, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        111, 102, 95, 100, 101, 99, 105, 100, 101, 95, 101, 113, 95, 116, 114, 117, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
        1819210885479960519 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0_value:
    leanh::LeanStringObject<104> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 104,
    m_capacity: 104,
    m_length: 103,
    m_data: [
        84, 104, 101, 32, 96, 100, 101, 99, 105, 100, 101, 95, 99, 98, 118, 96, 32, 117, 115, 97,
        103, 101, 32, 119, 97, 114, 110, 105, 110, 103, 32, 111, 112, 116, 105, 111, 110, 32, 105,
        115, 32, 101, 110, 97, 98, 108, 101, 100, 46, 32, 68, 105, 115, 97, 98, 108, 101, 32, 105,
        116, 32, 98, 121, 32, 115, 101, 116, 116, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111,
        112, 116, 105, 111, 110, 32, 99, 98, 118, 46, 119, 97, 114, 110, 105, 110, 103, 32, 102,
        97, 108, 115, 101, 96, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 99, 105, 100, 101, 95, 99, 98, 118, 0],
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0_value)
                as *mut leanh::LeanObject,
            11978265448379327237 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 68, 101, 99, 105, 100, 101, 67, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value) as *mut leanh::LeanObject,11560057156626128935 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value) as *mut leanh::LeanObject,12407121283116635999 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(
    mut v_opts_709_: *mut leanh::LeanObject,
    mut v_opt_710_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_711_ = leanh::lean_ctor_get(v_opt_710_, 0);
    v_defValue_712_ = leanh::lean_ctor_get(v_opt_710_, 1);
    v_map_713_ = leanh::lean_ctor_get(v_opts_709_, 0);
    v___x_714_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_713_,
            v_name_711_,
        );
    if leanh::lean_obj_tag(v___x_714_) == 0 {
        let mut v___x_715_: u8 = 0;
        v___x_715_ = (leanh::lean_unbox(v_defValue_712_) as u8);
        return v___x_715_;
    } else {
        let mut v_val_716_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_716_ = leanh::lean_ctor_get(v___x_714_, 0);
        leanh::lean_inc(v_val_716_);
        leanh::lean_dec_ref_known(v___x_714_, 1);
        if leanh::lean_obj_tag(v_val_716_) == 1 {
            let mut v_v_717_: u8 = 0;
            v_v_717_ = leanh::lean_ctor_get_uint8(v_val_716_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_716_, 0);
            return v_v_717_;
        } else {
            let mut v___x_718_: u8 = 0;
            leanh::lean_dec(v_val_716_);
            v___x_718_ = (leanh::lean_unbox(v_defValue_712_) as u8);
            return v___x_718_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(
    mut v_opts_719_: *mut leanh::LeanObject,
    mut v_opt_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_721_: u8 = 0;
    let mut v_r_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_721_ =
        l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_opts_719_, v_opt_720_);
    leanh::lean_dec_ref(v_opt_720_);
    leanh::lean_dec_ref(v_opts_719_);
    v_r_722_ = leanh::lean_box((v_res_721_) as usize);
    return v_r_722_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(
    mut v_snd_723_: u8,
    mut v_fst_724_: *mut leanh::LeanObject,
    mut v___y_725_: *mut leanh::LeanObject,
    mut v___y_726_: *mut leanh::LeanObject,
    mut v___y_727_: *mut leanh::LeanObject,
    mut v___y_728_: *mut leanh::LeanObject,
    mut v___y_729_: *mut leanh::LeanObject,
    mut v___y_730_: *mut leanh::LeanObject,
    mut v___y_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_743_: u8 = 0;
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_748_: u8 = 0;
    let mut v_unused_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_757_: u8 = 0;
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut v_a_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_765_: u8 = 0;
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_734_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_726_, v___y_729_, v___y_730_, v___y_731_, v___y_732_,
                );
                if leanh::lean_obj_tag(v___x_734_) == 0 {
                    v_a_735_ = leanh::lean_ctor_get(v___x_734_, 0);
                    leanh::lean_inc(v_a_735_);
                    leanh::lean_dec_ref_known(v___x_734_, 1);
                    v___x_736_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(
                        v_a_735_, v_snd_723_, v_fst_724_, v___y_729_, v___y_730_, v___y_731_,
                        v___y_732_,
                    );
                    if leanh::lean_obj_tag(v___x_736_) == 0 {
                        v_a_737_ = leanh::lean_ctor_get(v___x_736_, 0);
                        leanh::lean_inc(v_a_737_);
                        leanh::lean_dec_ref_known(v___x_736_, 1);
                        if leanh::lean_obj_tag(v_a_737_) == 0 {
                            v___x_750_ = leanh::lean_box(0);
                            v_a_739_ = v___x_750_;
                            state = 1;
                            continue;
                        } else {
                            v_val_751_ = leanh::lean_ctor_get(v_a_737_, 0);
                            leanh::lean_inc(v_val_751_);
                            leanh::lean_dec_ref_known(v_a_737_, 1);
                            v___x_752_ = leanh::lean_box(0);
                            v___x_753_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_753_, 0, v_val_751_);
                            leanh::lean_ctor_set(v___x_753_, 1, v___x_752_);
                            v_a_739_ = v___x_753_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_754_ = leanh::lean_ctor_get(v___x_736_, 0);
                        v_isSharedCheck_761_ = (!leanh::lean_is_exclusive(v___x_736_)) as u8;
                        if v_isSharedCheck_761_ == 0 {
                            v___x_756_ = v___x_736_;
                            v_isShared_757_ = v_isSharedCheck_761_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_754_);
                            leanh::lean_dec(v___x_736_);
                            v___x_756_ = leanh::lean_box(0);
                            v_isShared_757_ = v_isSharedCheck_761_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fst_724_);
                    v_a_762_ = leanh::lean_ctor_get(v___x_734_, 0);
                    v_isSharedCheck_769_ = (!leanh::lean_is_exclusive(v___x_734_)) as u8;
                    if v_isSharedCheck_769_ == 0 {
                        v___x_764_ = v___x_734_;
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_762_);
                        leanh::lean_dec(v___x_734_);
                        v___x_764_ = leanh::lean_box(0);
                        v_isShared_765_ = v_isSharedCheck_769_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_740_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_739_, v___y_726_, v___y_729_, v___y_730_, v___y_731_, v___y_732_,
                );
                if leanh::lean_obj_tag(v___x_740_) == 0 {
                    v_isSharedCheck_748_ = (!leanh::lean_is_exclusive(v___x_740_)) as u8;
                    if v_isSharedCheck_748_ == 0 {
                        v_unused_749_ = leanh::lean_ctor_get(v___x_740_, 0);
                        leanh::lean_dec(v_unused_749_);
                        v___x_742_ = v___x_740_;
                        v_isShared_743_ = v_isSharedCheck_748_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_740_);
                        v___x_742_ = leanh::lean_box(0);
                        v_isShared_743_ = v_isSharedCheck_748_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_740_;
                }
            }
            2 => {
                v___x_744_ = leanh::lean_box(0);
                if v_isShared_743_ == 0 {
                    leanh::lean_ctor_set(v___x_742_, 0, v___x_744_);
                    v___x_746_ = v___x_742_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_747_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
                    v___x_746_ = v_reuseFailAlloc_747_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_746_;
            }
            4 => {
                if v_isShared_757_ == 0 {
                    v___x_759_ = v___x_756_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
                    v___x_759_ = v_reuseFailAlloc_760_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_759_;
            }
            6 => {
                if v_isShared_765_ == 0 {
                    v___x_767_ = v___x_764_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
                    v___x_767_ = v_reuseFailAlloc_768_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(
    mut v_snd_770_: *mut leanh::LeanObject,
    mut v_fst_771_: *mut leanh::LeanObject,
    mut v___y_772_: *mut leanh::LeanObject,
    mut v___y_773_: *mut leanh::LeanObject,
    mut v___y_774_: *mut leanh::LeanObject,
    mut v___y_775_: *mut leanh::LeanObject,
    mut v___y_776_: *mut leanh::LeanObject,
    mut v___y_777_: *mut leanh::LeanObject,
    mut v___y_778_: *mut leanh::LeanObject,
    mut v___y_779_: *mut leanh::LeanObject,
    mut v___y_780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_5765__boxed_781_: u8 = 0;
    let mut v_res_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_5765__boxed_781_ = (leanh::lean_unbox(v_snd_770_) as u8);
    v_res_782_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(
        v_snd_5765__boxed_781_,
        v_fst_771_,
        v___y_772_,
        v___y_773_,
        v___y_774_,
        v___y_775_,
        v___y_776_,
        v___y_777_,
        v___y_778_,
        v___y_779_,
    );
    leanh::lean_dec(v___y_779_);
    leanh::lean_dec_ref(v___y_778_);
    leanh::lean_dec(v___y_777_);
    leanh::lean_dec_ref(v___y_776_);
    leanh::lean_dec(v___y_775_);
    leanh::lean_dec_ref(v___y_774_);
    leanh::lean_dec(v___y_773_);
    leanh::lean_dec_ref(v___y_772_);
    return v_res_782_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(
    mut v_msgData_783_: *mut leanh::LeanObject,
    mut v___y_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
    mut v___y_787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_789_ = lean_st_ref_get(v___y_787_);
    v_env_790_ = leanh::lean_ctor_get(v___x_789_, 0);
    leanh::lean_inc_ref(v_env_790_);
    leanh::lean_dec(v___x_789_);
    v___x_791_ = lean_st_ref_get(v___y_785_);
    v_mctx_792_ = leanh::lean_ctor_get(v___x_791_, 0);
    leanh::lean_inc_ref(v_mctx_792_);
    leanh::lean_dec(v___x_791_);
    v_lctx_793_ = leanh::lean_ctor_get(v___y_784_, 2);
    v_options_794_ = leanh::lean_ctor_get(v___y_786_, 2);
    leanh::lean_inc_ref(v_options_794_);
    leanh::lean_inc_ref(v_lctx_793_);
    v___x_795_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_795_, 0, v_env_790_);
    leanh::lean_ctor_set(v___x_795_, 1, v_mctx_792_);
    leanh::lean_ctor_set(v___x_795_, 2, v_lctx_793_);
    leanh::lean_ctor_set(v___x_795_, 3, v_options_794_);
    v___x_796_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_796_, 0, v___x_795_);
    leanh::lean_ctor_set(v___x_796_, 1, v_msgData_783_);
    v___x_797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_797_, 0, v___x_796_);
    return v___x_797_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_798_: *mut leanh::LeanObject,
    mut v___y_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
    mut v___y_802_: *mut leanh::LeanObject,
    mut v___y_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(v_msgData_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
    leanh::lean_dec(v___y_802_);
    leanh::lean_dec_ref(v___y_801_);
    leanh::lean_dec(v___y_800_);
    leanh::lean_dec_ref(v___y_799_);
    return v_res_804_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0(
    mut v___y_813_: u8,
    mut v_suppressElabErrors_814_: u8,
    mut v_x_815_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_815_) == 1 {
        let mut v_pre_816_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_816_ = leanh::lean_ctor_get(v_x_815_, 0);
        match leanh::lean_obj_tag(v_pre_816_) {
            1 => {
                let mut v_pre_817_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_817_ = leanh::lean_ctor_get(v_pre_816_, 0);
                match leanh::lean_obj_tag(v_pre_817_) {
                    0 => {
                        let mut v_str_818_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_819_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_821_: u8 = 0;
                        v_str_818_ = leanh::lean_ctor_get(v_x_815_, 1);
                        v_str_819_ = leanh::lean_ctor_get(v_pre_816_, 1);
                        v___x_820_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0;
                        v___x_821_ = lean_string_dec_eq(v_str_819_, v___x_820_);
                        if v___x_821_ == 0 {
                            let mut v___x_822_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_823_: u8 = 0;
                            v___x_822_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1;
                            v___x_823_ = lean_string_dec_eq(v_str_819_, v___x_822_);
                            if v___x_823_ == 0 {
                                return v___y_813_;
                            } else {
                                let mut v___x_824_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_825_: u8 = 0;
                                v___x_824_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2;
                                v___x_825_ = lean_string_dec_eq(v_str_818_, v___x_824_);
                                if v___x_825_ == 0 {
                                    return v___y_813_;
                                } else {
                                    return v_suppressElabErrors_814_;
                                }
                            }
                        } else {
                            let mut v___x_826_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_827_: u8 = 0;
                            v___x_826_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3;
                            v___x_827_ = lean_string_dec_eq(v_str_818_, v___x_826_);
                            if v___x_827_ == 0 {
                                return v___y_813_;
                            } else {
                                return v_suppressElabErrors_814_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_828_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_828_ = leanh::lean_ctor_get(v_pre_817_, 0);
                        if leanh::lean_obj_tag(v_pre_828_) == 0 {
                            let mut v_str_829_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_830_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_831_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_832_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_833_: u8 = 0;
                            v_str_829_ = leanh::lean_ctor_get(v_x_815_, 1);
                            v_str_830_ = leanh::lean_ctor_get(v_pre_816_, 1);
                            v_str_831_ = leanh::lean_ctor_get(v_pre_817_, 1);
                            v___x_832_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4;
                            v___x_833_ = lean_string_dec_eq(v_str_831_, v___x_832_);
                            if v___x_833_ == 0 {
                                return v___y_813_;
                            } else {
                                let mut v___x_834_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_835_: u8 = 0;
                                v___x_834_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5;
                                v___x_835_ = lean_string_dec_eq(v_str_830_, v___x_834_);
                                if v___x_835_ == 0 {
                                    return v___y_813_;
                                } else {
                                    let mut v___x_836_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_837_: u8 = 0;
                                    v___x_836_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6;
                                    v___x_837_ = lean_string_dec_eq(v_str_829_, v___x_836_);
                                    if v___x_837_ == 0 {
                                        return v___y_813_;
                                    } else {
                                        return v_suppressElabErrors_814_;
                                    }
                                }
                            }
                        } else {
                            return v___y_813_;
                        }
                    }
                    _ => {
                        return v___y_813_;
                    }
                }
            }
            0 => {
                let mut v_str_838_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_840_: u8 = 0;
                v_str_838_ = leanh::lean_ctor_get(v_x_815_, 1);
                v___x_839_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7;
                v___x_840_ = lean_string_dec_eq(v_str_838_, v___x_839_);
                if v___x_840_ == 0 {
                    return v___y_813_;
                } else {
                    return v_suppressElabErrors_814_;
                }
            }
            _ => {
                return v___y_813_;
            }
        }
    } else {
        return v___y_813_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(
    mut v___y_841_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_842_: *mut leanh::LeanObject,
    mut v_x_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5913__boxed_844_: u8 = 0;
    let mut v_suppressElabErrors_boxed_845_: u8 = 0;
    let mut v_res_846_: u8 = 0;
    let mut v_r_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_5913__boxed_844_ = (leanh::lean_unbox(v___y_841_) as u8);
    v_suppressElabErrors_boxed_845_ = (leanh::lean_unbox(v_suppressElabErrors_842_) as u8);
    v_res_846_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0(v___y_5913__boxed_844_, v_suppressElabErrors_boxed_845_, v_x_843_);
    leanh::lean_dec(v_x_843_);
    v_r_847_ = leanh::lean_box((v_res_846_) as usize);
    return v_r_847_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(
    mut v_ref_849_: *mut leanh::LeanObject,
    mut v_msgData_850_: *mut leanh::LeanObject,
    mut v_severity_851_: u8,
    mut v_isSilent_852_: u8,
    mut v___y_853_: *mut leanh::LeanObject,
    mut v___y_854_: *mut leanh::LeanObject,
    mut v___y_855_: *mut leanh::LeanObject,
    mut v___y_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_861_: u8 = 0;
    let mut v___y_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_865_: u8 = 0;
    let mut v___y_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v___y_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_897_: u8 = 0;
    let mut v___y_898_: u8 = 0;
    let mut v___y_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_900_: u8 = 0;
    let mut v___y_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_908_: u8 = 0;
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: u8 = 0;
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_918_: u8 = 0;
    let mut v___y_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_921_: u8 = 0;
    let mut v___y_922_: u8 = 0;
    let mut v___y_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_926_: u8 = 0;
    let mut v___y_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_933_: u8 = 0;
    let mut v___y_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_935_: u8 = 0;
    let mut v___y_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_937_: u8 = 0;
    let mut v_ref_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___y_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_945_: u8 = 0;
    let mut v___y_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_949_: u8 = 0;
    let mut v___y_950_: u8 = 0;
    let mut v___y_952_: u8 = 0;
    let mut v_fileName_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_957_: u8 = 0;
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u8 = 0;
    let mut v___x_962_: u8 = 0;
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v___x_968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_942_ = 2;
                v___x_967_ = l_Lean_instBEqMessageSeverity_beq(v_severity_851_, v___x_942_);
                if v___x_967_ == 0 {
                    v___y_952_ = v___x_967_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_850_);
                    v___x_968_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_850_);
                    v___y_952_ = v___x_968_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_868_ = lean_st_ref_take(v___y_867_);
                v_currNamespace_869_ = leanh::lean_ctor_get(v___y_866_, 6);
                v_openDecls_870_ = leanh::lean_ctor_get(v___y_866_, 7);
                v_env_871_ = leanh::lean_ctor_get(v___x_868_, 0);
                v_nextMacroScope_872_ = leanh::lean_ctor_get(v___x_868_, 1);
                v_ngen_873_ = leanh::lean_ctor_get(v___x_868_, 2);
                v_auxDeclNGen_874_ = leanh::lean_ctor_get(v___x_868_, 3);
                v_traceState_875_ = leanh::lean_ctor_get(v___x_868_, 4);
                v_cache_876_ = leanh::lean_ctor_get(v___x_868_, 5);
                v_messages_877_ = leanh::lean_ctor_get(v___x_868_, 6);
                v_infoState_878_ = leanh::lean_ctor_get(v___x_868_, 7);
                v_snapshotTasks_879_ = leanh::lean_ctor_get(v___x_868_, 8);
                v_isSharedCheck_893_ = (!leanh::lean_is_exclusive(v___x_868_)) as u8;
                if v_isSharedCheck_893_ == 0 {
                    v___x_881_ = v___x_868_;
                    v_isShared_882_ = v_isSharedCheck_893_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_879_);
                    leanh::lean_inc(v_infoState_878_);
                    leanh::lean_inc(v_messages_877_);
                    leanh::lean_inc(v_cache_876_);
                    leanh::lean_inc(v_traceState_875_);
                    leanh::lean_inc(v_auxDeclNGen_874_);
                    leanh::lean_inc(v_ngen_873_);
                    leanh::lean_inc(v_nextMacroScope_872_);
                    leanh::lean_inc(v_env_871_);
                    leanh::lean_dec(v___x_868_);
                    v___x_881_ = leanh::lean_box(0);
                    v_isShared_882_ = v_isSharedCheck_893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_870_);
                leanh::lean_inc(v_currNamespace_869_);
                v___x_883_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_883_, 0, v_currNamespace_869_);
                leanh::lean_ctor_set(v___x_883_, 1, v_openDecls_870_);
                v___x_884_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_884_, 0, v___x_883_);
                leanh::lean_ctor_set(v___x_884_, 1, v___y_864_);
                leanh::lean_inc_ref(v___y_859_);
                leanh::lean_inc_ref(v___y_863_);
                v___x_885_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_885_, 0, v___y_863_);
                leanh::lean_ctor_set(v___x_885_, 1, v___y_862_);
                leanh::lean_ctor_set(v___x_885_, 2, v___y_860_);
                leanh::lean_ctor_set(v___x_885_, 3, v___y_859_);
                leanh::lean_ctor_set(v___x_885_, 4, v___x_884_);
                leanh::lean_ctor_set_uint8(
                    v___x_885_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_865_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_885_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_861_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_885_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_852_,
                );
                v___x_886_ = l_Lean_MessageLog_add(v___x_885_, v_messages_877_);
                if v_isShared_882_ == 0 {
                    leanh::lean_ctor_set(v___x_881_, 6, v___x_886_);
                    v___x_888_ = v___x_881_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_env_871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 1, v_nextMacroScope_872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 2, v_ngen_873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 3, v_auxDeclNGen_874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 4, v_traceState_875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 5, v_cache_876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 6, v___x_886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 7, v_infoState_878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 8, v_snapshotTasks_879_);
                    v___x_888_ = v_reuseFailAlloc_892_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_889_ = lean_st_ref_set(v___y_867_, v___x_888_);
                v___x_890_ = leanh::lean_box(0);
                v___x_891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_891_, 0, v___x_890_);
                return v___x_891_;
            }
            4 => {
                v___x_903_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_850_,
                    );
                v___x_904_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(v___x_903_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
                v_a_905_ = leanh::lean_ctor_get(v___x_904_, 0);
                v_isSharedCheck_918_ = (!leanh::lean_is_exclusive(v___x_904_)) as u8;
                if v_isSharedCheck_918_ == 0 {
                    v___x_907_ = v___x_904_;
                    v_isShared_908_ = v_isSharedCheck_918_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_905_);
                    leanh::lean_dec(v___x_904_);
                    v___x_907_ = leanh::lean_box(0);
                    v_isShared_908_ = v_isSharedCheck_918_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_901_, 2);
                v___x_909_ = l_Lean_FileMap_toPosition(v___y_901_, v___y_896_);
                leanh::lean_dec(v___y_896_);
                v___x_910_ = l_Lean_FileMap_toPosition(v___y_901_, v___y_902_);
                leanh::lean_dec(v___y_902_);
                v___x_911_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_911_, 0, v___x_910_);
                v___x_912_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0;
                if v___y_897_ == 0 {
                    leanh::lean_del_object(v___x_907_);
                    leanh::lean_dec_ref(v___y_895_);
                    v___y_859_ = v___x_912_;
                    v___y_860_ = v___x_911_;
                    v___y_861_ = v___y_898_;
                    v___y_862_ = v___x_909_;
                    v___y_863_ = v___y_899_;
                    v___y_864_ = v_a_905_;
                    v___y_865_ = v___y_900_;
                    v___y_866_ = v___y_855_;
                    v___y_867_ = v___y_856_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_905_);
                    v___x_913_ = l_Lean_MessageData_hasTag(v___y_895_, v_a_905_);
                    if v___x_913_ == 0 {
                        leanh::lean_dec_ref_known(v___x_911_, 1);
                        leanh::lean_dec_ref(v___x_909_);
                        leanh::lean_dec(v_a_905_);
                        v___x_914_ = leanh::lean_box(0);
                        if v_isShared_908_ == 0 {
                            leanh::lean_ctor_set(v___x_907_, 0, v___x_914_);
                            v___x_916_ = v___x_907_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_917_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
                            v___x_916_ = v_reuseFailAlloc_917_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_907_);
                        v___y_859_ = v___x_912_;
                        v___y_860_ = v___x_911_;
                        v___y_861_ = v___y_898_;
                        v___y_862_ = v___x_909_;
                        v___y_863_ = v___y_899_;
                        v___y_864_ = v_a_905_;
                        v___y_865_ = v___y_900_;
                        v___y_866_ = v___y_855_;
                        v___y_867_ = v___y_856_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_916_;
            }
            7 => {
                v___x_928_ = l_Lean_Syntax_getTailPos_x3f(v___y_924_, v___y_926_);
                leanh::lean_dec(v___y_924_);
                if leanh::lean_obj_tag(v___x_928_) == 0 {
                    leanh::lean_inc(v___y_927_);
                    v___y_895_ = v___y_920_;
                    v___y_896_ = v___y_927_;
                    v___y_897_ = v___y_921_;
                    v___y_898_ = v___y_922_;
                    v___y_899_ = v___y_923_;
                    v___y_900_ = v___y_926_;
                    v___y_901_ = v___y_925_;
                    v___y_902_ = v___y_927_;
                    state = 4;
                    continue;
                } else {
                    v_val_929_ = leanh::lean_ctor_get(v___x_928_, 0);
                    leanh::lean_inc(v_val_929_);
                    leanh::lean_dec_ref_known(v___x_928_, 1);
                    v___y_895_ = v___y_920_;
                    v___y_896_ = v___y_927_;
                    v___y_897_ = v___y_921_;
                    v___y_898_ = v___y_922_;
                    v___y_899_ = v___y_923_;
                    v___y_900_ = v___y_926_;
                    v___y_901_ = v___y_925_;
                    v___y_902_ = v_val_929_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_938_ = l_Lean_replaceRef(v_ref_849_, v___y_932_);
                v___x_939_ = l_Lean_Syntax_getPos_x3f(v_ref_938_, v___y_935_);
                if leanh::lean_obj_tag(v___x_939_) == 0 {
                    v___x_940_ = leanh::lean_unsigned_to_nat(0);
                    v___y_920_ = v___y_931_;
                    v___y_921_ = v___y_933_;
                    v___y_922_ = v___y_937_;
                    v___y_923_ = v___y_934_;
                    v___y_924_ = v_ref_938_;
                    v___y_925_ = v___y_936_;
                    v___y_926_ = v___y_935_;
                    v___y_927_ = v___x_940_;
                    state = 7;
                    continue;
                } else {
                    v_val_941_ = leanh::lean_ctor_get(v___x_939_, 0);
                    leanh::lean_inc(v_val_941_);
                    leanh::lean_dec_ref_known(v___x_939_, 1);
                    v___y_920_ = v___y_931_;
                    v___y_921_ = v___y_933_;
                    v___y_922_ = v___y_937_;
                    v___y_923_ = v___y_934_;
                    v___y_924_ = v_ref_938_;
                    v___y_925_ = v___y_936_;
                    v___y_926_ = v___y_935_;
                    v___y_927_ = v_val_941_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_950_ == 0 {
                    v___y_931_ = v___y_946_;
                    v___y_932_ = v___y_944_;
                    v___y_933_ = v___y_945_;
                    v___y_934_ = v___y_947_;
                    v___y_935_ = v___y_949_;
                    v___y_936_ = v___y_948_;
                    v___y_937_ = v_severity_851_;
                    state = 8;
                    continue;
                } else {
                    v___y_931_ = v___y_946_;
                    v___y_932_ = v___y_944_;
                    v___y_933_ = v___y_945_;
                    v___y_934_ = v___y_947_;
                    v___y_935_ = v___y_949_;
                    v___y_936_ = v___y_948_;
                    v___y_937_ = v___x_942_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_952_ == 0 {
                    v_fileName_953_ = leanh::lean_ctor_get(v___y_855_, 0);
                    v_fileMap_954_ = leanh::lean_ctor_get(v___y_855_, 1);
                    v_options_955_ = leanh::lean_ctor_get(v___y_855_, 2);
                    v_ref_956_ = leanh::lean_ctor_get(v___y_855_, 5);
                    v_suppressElabErrors_957_ = leanh::lean_ctor_get_uint8(
                        v___y_855_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_958_ = leanh::lean_box((v___y_952_) as usize);
                    v___x_959_ = leanh::lean_box((v_suppressElabErrors_957_) as usize);
                    v___f_960_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_960_, 0, v___x_958_);
                    leanh::lean_closure_set(v___f_960_, 1, v___x_959_);
                    v___x_961_ = 1;
                    v___x_962_ = l_Lean_instBEqMessageSeverity_beq(v_severity_851_, v___x_961_);
                    if v___x_962_ == 0 {
                        v___y_944_ = v_ref_956_;
                        v___y_945_ = v_suppressElabErrors_957_;
                        v___y_946_ = v___f_960_;
                        v___y_947_ = v_fileName_953_;
                        v___y_948_ = v_fileMap_954_;
                        v___y_949_ = v___y_952_;
                        v___y_950_ = v___x_962_;
                        state = 9;
                        continue;
                    } else {
                        v___x_963_ = l_Lean_warningAsError;
                        v___x_964_ =
                            l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(
                                v_options_955_,
                                v___x_963_,
                            );
                        v___y_944_ = v_ref_956_;
                        v___y_945_ = v_suppressElabErrors_957_;
                        v___y_946_ = v___f_960_;
                        v___y_947_ = v_fileName_953_;
                        v___y_948_ = v_fileMap_954_;
                        v___y_949_ = v___y_952_;
                        v___y_950_ = v___x_964_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_850_);
                    v___x_965_ = leanh::lean_box(0);
                    v___x_966_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_966_, 0, v___x_965_);
                    return v___x_966_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___boxed(
    mut v_ref_969_: *mut leanh::LeanObject,
    mut v_msgData_970_: *mut leanh::LeanObject,
    mut v_severity_971_: *mut leanh::LeanObject,
    mut v_isSilent_972_: *mut leanh::LeanObject,
    mut v___y_973_: *mut leanh::LeanObject,
    mut v___y_974_: *mut leanh::LeanObject,
    mut v___y_975_: *mut leanh::LeanObject,
    mut v___y_976_: *mut leanh::LeanObject,
    mut v___y_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_978_: u8 = 0;
    let mut v_isSilent_boxed_979_: u8 = 0;
    let mut v_res_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_978_ = (leanh::lean_unbox(v_severity_971_) as u8);
    v_isSilent_boxed_979_ = (leanh::lean_unbox(v_isSilent_972_) as u8);
    v_res_980_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(v_ref_969_, v_msgData_970_, v_severity_boxed_978_, v_isSilent_boxed_979_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
    leanh::lean_dec(v___y_976_);
    leanh::lean_dec_ref(v___y_975_);
    leanh::lean_dec(v___y_974_);
    leanh::lean_dec_ref(v___y_973_);
    leanh::lean_dec(v_ref_969_);
    return v_res_980_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(
    mut v_ref_981_: *mut leanh::LeanObject,
    mut v_msgData_982_: *mut leanh::LeanObject,
    mut v___y_983_: *mut leanh::LeanObject,
    mut v___y_984_: *mut leanh::LeanObject,
    mut v___y_985_: *mut leanh::LeanObject,
    mut v___y_986_: *mut leanh::LeanObject,
    mut v___y_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
    mut v___y_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_992_: u8 = 0;
    let mut v___x_993_: u8 = 0;
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = 1;
    v___x_993_ = 0;
    v___x_994_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(v_ref_981_, v_msgData_982_, v___x_992_, v___x_993_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
    return v___x_994_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(
    mut v_ref_995_: *mut leanh::LeanObject,
    mut v_msgData_996_: *mut leanh::LeanObject,
    mut v___y_997_: *mut leanh::LeanObject,
    mut v___y_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(
        v_ref_995_,
        v_msgData_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___y_1002_,
        v___y_1003_,
        v___y_1004_,
    );
    leanh::lean_dec(v___y_1004_);
    leanh::lean_dec_ref(v___y_1003_);
    leanh::lean_dec(v___y_1002_);
    leanh::lean_dec_ref(v___y_1001_);
    leanh::lean_dec(v___y_1000_);
    leanh::lean_dec_ref(v___y_999_);
    leanh::lean_dec(v___y_998_);
    leanh::lean_dec_ref(v___y_997_);
    leanh::lean_dec(v_ref_995_);
    return v_res_1006_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1;
    v___x_1011_ = l_Lean_MessageData_ofFormat(v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(
    mut v_stx_1012_: *mut leanh::LeanObject,
    mut v___y_1013_: *mut leanh::LeanObject,
    mut v___y_1014_: *mut leanh::LeanObject,
    mut v___y_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
    mut v___y_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1024_: u8 = 0;
    let mut v___y_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u8 = 0;
    let mut v_a_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_a_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1068_: u8 = 0;
    let mut v_hypotheses_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1070_: u8 = 0;
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1076_: u8 = 0;
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_options_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: u8 = 0;
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1081_ = leanh::lean_ctor_get(v___y_1019_, 2);
                v___x_1082_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
                v___x_1083_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(
                    v_options_1081_,
                    v___x_1082_,
                );
                if v___x_1083_ == 0 {
                    v___y_1037_ = v___y_1013_;
                    v___y_1038_ = v___y_1014_;
                    v___y_1039_ = v___y_1015_;
                    v___y_1040_ = v___y_1016_;
                    v___y_1041_ = v___y_1017_;
                    v___y_1042_ = v___y_1018_;
                    v___y_1043_ = v___y_1019_;
                    v___y_1044_ = v___y_1020_;
                    state = 2;
                    continue;
                } else {
                    v___x_1084_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2,
                    );
                    v___x_1085_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(
                        v_stx_1012_,
                        v___x_1084_,
                        v___y_1013_,
                        v___y_1014_,
                        v___y_1015_,
                        v___y_1016_,
                        v___y_1017_,
                        v___y_1018_,
                        v___y_1019_,
                        v___y_1020_,
                    );
                    if leanh::lean_obj_tag(v___x_1085_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1085_, 1);
                        v___y_1037_ = v___y_1013_;
                        v___y_1038_ = v___y_1014_;
                        v___y_1039_ = v___y_1015_;
                        v___y_1040_ = v___y_1016_;
                        v___y_1041_ = v___y_1017_;
                        v___y_1042_ = v___y_1018_;
                        v___y_1043_ = v___y_1019_;
                        v___y_1044_ = v___y_1020_;
                        state = 2;
                        continue;
                    } else {
                        return v___x_1085_;
                    }
                }
            }
            1 => {
                v___x_1033_ = leanh::lean_box((v_snd_1024_) as usize);
                v___f_1034_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    2,
                );
                leanh::lean_closure_set(v___f_1034_, 0, v___x_1033_);
                leanh::lean_closure_set(v___f_1034_, 1, v_fst_1023_);
                v___x_1035_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_1034_,
                    v___y_1025_,
                    v___y_1026_,
                    v___y_1027_,
                    v___y_1028_,
                    v___y_1029_,
                    v___y_1030_,
                    v___y_1031_,
                    v___y_1032_,
                );
                return v___x_1035_;
            }
            2 => {
                v___x_1045_ = leanh::lean_unsigned_to_nat(1);
                v___x_1046_ = l_Lean_Syntax_getArg(v_stx_1012_, v___x_1045_);
                v___x_1047_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1046_);
                leanh::lean_dec(v___x_1046_);
                if leanh::lean_obj_tag(v___x_1047_) == 0 {
                    v___x_1048_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_1038_,
                        v___y_1041_,
                        v___y_1042_,
                        v___y_1043_,
                        v___y_1044_,
                    );
                    if leanh::lean_obj_tag(v___x_1048_) == 0 {
                        v_a_1049_ = leanh::lean_ctor_get(v___x_1048_, 0);
                        leanh::lean_inc(v_a_1049_);
                        leanh::lean_dec_ref_known(v___x_1048_, 1);
                        v___x_1050_ = l_Lean_MVarId_getNondepPropHyps(
                            v_a_1049_,
                            v___y_1041_,
                            v___y_1042_,
                            v___y_1043_,
                            v___y_1044_,
                        );
                        if leanh::lean_obj_tag(v___x_1050_) == 0 {
                            v_a_1051_ = leanh::lean_ctor_get(v___x_1050_, 0);
                            leanh::lean_inc(v_a_1051_);
                            leanh::lean_dec_ref_known(v___x_1050_, 1);
                            v___x_1052_ = 1;
                            v_fst_1023_ = v_a_1051_;
                            v_snd_1024_ = v___x_1052_;
                            v___y_1025_ = v___y_1037_;
                            v___y_1026_ = v___y_1038_;
                            v___y_1027_ = v___y_1039_;
                            v___y_1028_ = v___y_1040_;
                            v___y_1029_ = v___y_1041_;
                            v___y_1030_ = v___y_1042_;
                            v___y_1031_ = v___y_1043_;
                            v___y_1032_ = v___y_1044_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1053_ = leanh::lean_ctor_get(v___x_1050_, 0);
                            v_isSharedCheck_1060_ =
                                (!leanh::lean_is_exclusive(v___x_1050_)) as u8;
                            if v_isSharedCheck_1060_ == 0 {
                                v___x_1055_ = v___x_1050_;
                                v_isShared_1056_ = v_isSharedCheck_1060_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1053_);
                                leanh::lean_dec(v___x_1050_);
                                v___x_1055_ = leanh::lean_box(0);
                                v_isShared_1056_ = v_isSharedCheck_1060_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_1061_ = leanh::lean_ctor_get(v___x_1048_, 0);
                        v_isSharedCheck_1068_ =
                            (!leanh::lean_is_exclusive(v___x_1048_)) as u8;
                        if v_isSharedCheck_1068_ == 0 {
                            v___x_1063_ = v___x_1048_;
                            v_isShared_1064_ = v_isSharedCheck_1068_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1061_);
                            leanh::lean_dec(v___x_1048_);
                            v___x_1063_ = leanh::lean_box(0);
                            v_isShared_1064_ = v_isSharedCheck_1068_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_hypotheses_1069_ = leanh::lean_ctor_get(v___x_1047_, 0);
                    leanh::lean_inc_ref(v_hypotheses_1069_);
                    v_type_1070_ = leanh::lean_ctor_get_uint8(
                        v___x_1047_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v___x_1047_, 1);
                    v___x_1071_ = l_Lean_Elab_Tactic_getFVarIds(
                        v_hypotheses_1069_,
                        v___y_1037_,
                        v___y_1038_,
                        v___y_1039_,
                        v___y_1040_,
                        v___y_1041_,
                        v___y_1042_,
                        v___y_1043_,
                        v___y_1044_,
                    );
                    if leanh::lean_obj_tag(v___x_1071_) == 0 {
                        v_a_1072_ = leanh::lean_ctor_get(v___x_1071_, 0);
                        leanh::lean_inc(v_a_1072_);
                        leanh::lean_dec_ref_known(v___x_1071_, 1);
                        v_fst_1023_ = v_a_1072_;
                        v_snd_1024_ = v_type_1070_;
                        v___y_1025_ = v___y_1037_;
                        v___y_1026_ = v___y_1038_;
                        v___y_1027_ = v___y_1039_;
                        v___y_1028_ = v___y_1040_;
                        v___y_1029_ = v___y_1041_;
                        v___y_1030_ = v___y_1042_;
                        v___y_1031_ = v___y_1043_;
                        v___y_1032_ = v___y_1044_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1073_ = leanh::lean_ctor_get(v___x_1071_, 0);
                        v_isSharedCheck_1080_ =
                            (!leanh::lean_is_exclusive(v___x_1071_)) as u8;
                        if v_isSharedCheck_1080_ == 0 {
                            v___x_1075_ = v___x_1071_;
                            v_isShared_1076_ = v_isSharedCheck_1080_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1073_);
                            leanh::lean_dec(v___x_1071_);
                            v___x_1075_ = leanh::lean_box(0);
                            v_isShared_1076_ = v_isSharedCheck_1080_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1056_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1058_;
            }
            5 => {
                if v_isShared_1064_ == 0 {
                    v___x_1066_ = v___x_1063_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1067_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
                    v___x_1066_ = v_reuseFailAlloc_1067_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1066_;
            }
            7 => {
                if v_isShared_1076_ == 0 {
                    v___x_1078_ = v___x_1075_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(
    mut v_stx_1086_: *mut leanh::LeanObject,
    mut v___y_1087_: *mut leanh::LeanObject,
    mut v___y_1088_: *mut leanh::LeanObject,
    mut v___y_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
    mut v___y_1094_: *mut leanh::LeanObject,
    mut v___y_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(
        v_stx_1086_,
        v___y_1087_,
        v___y_1088_,
        v___y_1089_,
        v___y_1090_,
        v___y_1091_,
        v___y_1092_,
        v___y_1093_,
        v___y_1094_,
    );
    leanh::lean_dec(v___y_1094_);
    leanh::lean_dec_ref(v___y_1093_);
    leanh::lean_dec(v___y_1092_);
    leanh::lean_dec_ref(v___y_1091_);
    leanh::lean_dec(v___y_1090_);
    leanh::lean_dec_ref(v___y_1089_);
    leanh::lean_dec(v___y_1088_);
    leanh::lean_dec_ref(v___y_1087_);
    leanh::lean_dec(v_stx_1086_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalCbv(
    mut v_stx_1097_: *mut leanh::LeanObject,
    mut v_a_1098_: *mut leanh::LeanObject,
    mut v_a_1099_: *mut leanh::LeanObject,
    mut v_a_1100_: *mut leanh::LeanObject,
    mut v_a_1101_: *mut leanh::LeanObject,
    mut v_a_1102_: *mut leanh::LeanObject,
    mut v_a_1103_: *mut leanh::LeanObject,
    mut v_a_1104_: *mut leanh::LeanObject,
    mut v_a_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1107_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    leanh::lean_closure_set(v___f_1107_, 0, v_stx_1097_);
    v___x_1108_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_1107_,
        v_a_1098_,
        v_a_1099_,
        v_a_1100_,
        v_a_1101_,
        v_a_1102_,
        v_a_1103_,
        v_a_1104_,
        v_a_1105_,
    );
    return v___x_1108_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalCbv___boxed(
    mut v_stx_1109_: *mut leanh::LeanObject,
    mut v_a_1110_: *mut leanh::LeanObject,
    mut v_a_1111_: *mut leanh::LeanObject,
    mut v_a_1112_: *mut leanh::LeanObject,
    mut v_a_1113_: *mut leanh::LeanObject,
    mut v_a_1114_: *mut leanh::LeanObject,
    mut v_a_1115_: *mut leanh::LeanObject,
    mut v_a_1116_: *mut leanh::LeanObject,
    mut v_a_1117_: *mut leanh::LeanObject,
    mut v_a_1118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1119_ = l_Lean_Elab_Tactic_Cbv_evalCbv(
        v_stx_1109_,
        v_a_1110_,
        v_a_1111_,
        v_a_1112_,
        v_a_1113_,
        v_a_1114_,
        v_a_1115_,
        v_a_1116_,
        v_a_1117_,
    );
    leanh::lean_dec(v_a_1117_);
    leanh::lean_dec_ref(v_a_1116_);
    leanh::lean_dec(v_a_1115_);
    leanh::lean_dec_ref(v_a_1114_);
    leanh::lean_dec(v_a_1113_);
    leanh::lean_dec_ref(v_a_1112_);
    leanh::lean_dec(v_a_1111_);
    leanh::lean_dec_ref(v_a_1110_);
    return v_res_1119_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1(
    mut v_ref_1120_: *mut leanh::LeanObject,
    mut v_msgData_1121_: *mut leanh::LeanObject,
    mut v_severity_1122_: u8,
    mut v_isSilent_1123_: u8,
    mut v___y_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
    mut v___y_1127_: *mut leanh::LeanObject,
    mut v___y_1128_: *mut leanh::LeanObject,
    mut v___y_1129_: *mut leanh::LeanObject,
    mut v___y_1130_: *mut leanh::LeanObject,
    mut v___y_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(v_ref_1120_, v_msgData_1121_, v_severity_1122_, v_isSilent_1123_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
    return v___x_1133_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___boxed(
    mut v_ref_1134_: *mut leanh::LeanObject,
    mut v_msgData_1135_: *mut leanh::LeanObject,
    mut v_severity_1136_: *mut leanh::LeanObject,
    mut v_isSilent_1137_: *mut leanh::LeanObject,
    mut v___y_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v___y_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
    mut v___y_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
    mut v___y_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_1147_: u8 = 0;
    let mut v_isSilent_boxed_1148_: u8 = 0;
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1147_ = (leanh::lean_unbox(v_severity_1136_) as u8);
    v_isSilent_boxed_1148_ = (leanh::lean_unbox(v_isSilent_1137_) as u8);
    v_res_1149_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1(v_ref_1134_, v_msgData_1135_, v_severity_boxed_1147_, v_isSilent_boxed_1148_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
    leanh::lean_dec(v___y_1145_);
    leanh::lean_dec_ref(v___y_1144_);
    leanh::lean_dec(v___y_1143_);
    leanh::lean_dec_ref(v___y_1142_);
    leanh::lean_dec(v___y_1141_);
    leanh::lean_dec_ref(v___y_1140_);
    leanh::lean_dec(v___y_1139_);
    leanh::lean_dec_ref(v___y_1138_);
    leanh::lean_dec(v_ref_1134_);
    return v_res_1149_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1()
-> *mut leanh::LeanObject {
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1167_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1168_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3;
    v___x_1169_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6;
    v___x_1170_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Cbv_evalCbv___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1171_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1167_,
        v___x_1168_,
        v___x_1169_,
        v___x_1170_,
    );
    return v___x_1171_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(
    mut v_a_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
    return v_res_1173_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = leanh::lean_box(0);
    v___x_1175_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1176_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1176_, 0, v___x_1175_);
    leanh::lean_ctor_set(v___x_1176_, 1, v___x_1174_);
    return v___x_1176_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0);
    v___x_1179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1179_, 0, v___x_1178_);
    return v___x_1179_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(
    mut v___y_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg();
    return v_res_1181_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(
    mut v_00_u03b1_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
    mut v___y_1186_: *mut leanh::LeanObject,
    mut v___y_1187_: *mut leanh::LeanObject,
    mut v___y_1188_: *mut leanh::LeanObject,
    mut v___y_1189_: *mut leanh::LeanObject,
    mut v___y_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg();
    return v___x_1192_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(
    mut v_00_u03b1_1193_: *mut leanh::LeanObject,
    mut v___y_1194_: *mut leanh::LeanObject,
    mut v___y_1195_: *mut leanh::LeanObject,
    mut v___y_1196_: *mut leanh::LeanObject,
    mut v___y_1197_: *mut leanh::LeanObject,
    mut v___y_1198_: *mut leanh::LeanObject,
    mut v___y_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
    mut v___y_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(
            v_00_u03b1_1193_,
            v___y_1194_,
            v___y_1195_,
            v___y_1196_,
            v___y_1197_,
            v___y_1198_,
            v___y_1199_,
            v___y_1200_,
            v___y_1201_,
        );
    leanh::lean_dec(v___y_1201_);
    leanh::lean_dec_ref(v___y_1200_);
    leanh::lean_dec(v___y_1199_);
    leanh::lean_dec_ref(v___y_1198_);
    leanh::lean_dec(v___y_1197_);
    leanh::lean_dec_ref(v___y_1196_);
    leanh::lean_dec(v___y_1195_);
    leanh::lean_dec_ref(v___y_1194_);
    return v_res_1203_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(
    mut v_msg_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1215_: u8 = 0;
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1210_ = leanh::lean_ctor_get(v___y_1207_, 5);
                v___x_1211_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(v_msg_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
                v_a_1212_ = leanh::lean_ctor_get(v___x_1211_, 0);
                v_isSharedCheck_1220_ = (!leanh::lean_is_exclusive(v___x_1211_)) as u8;
                if v_isSharedCheck_1220_ == 0 {
                    v___x_1214_ = v___x_1211_;
                    v_isShared_1215_ = v_isSharedCheck_1220_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1212_);
                    leanh::lean_dec(v___x_1211_);
                    v___x_1214_ = leanh::lean_box(0);
                    v_isShared_1215_ = v_isSharedCheck_1220_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1210_);
                v___x_1216_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1216_, 0, v_ref_1210_);
                leanh::lean_ctor_set(v___x_1216_, 1, v_a_1212_);
                if v_isShared_1215_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1214_, 1);
                    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1216_);
                    v___x_1218_ = v___x_1214_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
                    v___x_1218_ = v_reuseFailAlloc_1219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(
    mut v_msg_1221_: *mut leanh::LeanObject,
    mut v___y_1222_: *mut leanh::LeanObject,
    mut v___y_1223_: *mut leanh::LeanObject,
    mut v___y_1224_: *mut leanh::LeanObject,
    mut v___y_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1227_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(
        v_msg_1221_,
        v___y_1222_,
        v___y_1223_,
        v___y_1224_,
        v___y_1225_,
    );
    leanh::lean_dec(v___y_1225_);
    leanh::lean_dec_ref(v___y_1224_);
    leanh::lean_dec(v___y_1223_);
    leanh::lean_dec_ref(v___y_1222_);
    return v_res_1227_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0;
    v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
    return v___x_1230_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(
    mut v_x_1231_: *mut leanh::LeanObject,
    mut v___y_1232_: *mut leanh::LeanObject,
    mut v___y_1233_: *mut leanh::LeanObject,
    mut v___y_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1,
    );
    v___x_1238_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(
        v___x_1237_,
        v___y_1232_,
        v___y_1233_,
        v___y_1234_,
        v___y_1235_,
    );
    return v___x_1238_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed(
    mut v_x_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
    mut v___y_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1245_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(
        v_x_1239_,
        v___y_1240_,
        v___y_1241_,
        v___y_1242_,
        v___y_1243_,
    );
    leanh::lean_dec(v___y_1243_);
    leanh::lean_dec_ref(v___y_1242_);
    leanh::lean_dec(v___y_1241_);
    leanh::lean_dec_ref(v___y_1240_);
    leanh::lean_dec(v_x_1239_);
    return v_res_1245_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(
    mut v___x_1249_: u8,
    mut v___f_1250_: *mut leanh::LeanObject,
    mut v___y_1251_: *mut leanh::LeanObject,
    mut v___y_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
    mut v___y_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_unused_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut v_a_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1273_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_1252_,
                    v___y_1255_,
                    v___y_1256_,
                    v___y_1257_,
                    v___y_1258_,
                );
                if leanh::lean_obj_tag(v___x_1273_) == 0 {
                    v_a_1274_ = leanh::lean_ctor_get(v___x_1273_, 0);
                    leanh::lean_inc(v_a_1274_);
                    leanh::lean_dec_ref_known(v___x_1273_, 1);
                    v___x_1275_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1;
                    v___x_1276_ = 0;
                    v___x_1277_ = 0;
                    v___x_1278_ = leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    leanh::lean_ctor_set_uint8(v___x_1278_, 0 as u32, v___x_1276_);
                    leanh::lean_ctor_set_uint8(v___x_1278_, 1 as u32, v___x_1249_);
                    leanh::lean_ctor_set_uint8(v___x_1278_, 2 as u32, v___x_1277_);
                    leanh::lean_ctor_set_uint8(v___x_1278_, 3 as u32, v___x_1249_);
                    v___x_1279_ = l_Lean_MVarId_applyConst(
                        v_a_1274_,
                        v___x_1275_,
                        v___x_1278_,
                        v___y_1255_,
                        v___y_1256_,
                        v___y_1257_,
                        v___y_1258_,
                    );
                    if leanh::lean_obj_tag(v___x_1279_) == 0 {
                        v_a_1280_ = leanh::lean_ctor_get(v___x_1279_, 0);
                        leanh::lean_inc(v_a_1280_);
                        leanh::lean_dec_ref_known(v___x_1279_, 1);
                        if leanh::lean_obj_tag(v_a_1280_) == 1 {
                            v_tail_1281_ = leanh::lean_ctor_get(v_a_1280_, 1);
                            if leanh::lean_obj_tag(v_tail_1281_) == 0 {
                                leanh::lean_dec_ref(v___f_1250_);
                                v_head_1282_ = leanh::lean_ctor_get(v_a_1280_, 0);
                                leanh::lean_inc(v_head_1282_);
                                leanh::lean_dec_ref_known(v_a_1280_, 2);
                                v___x_1283_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(
                                    v_head_1282_,
                                    v___y_1255_,
                                    v___y_1256_,
                                    v___y_1257_,
                                    v___y_1258_,
                                );
                                v___y_1261_ = v___x_1283_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v___y_1258_);
                                leanh::lean_inc_ref(v___y_1257_);
                                leanh::lean_inc(v___y_1256_);
                                leanh::lean_inc_ref(v___y_1255_);
                                v___x_1284_ = leanh::lean_apply_6(
                                    v___f_1250_,
                                    v_a_1280_,
                                    v___y_1255_,
                                    v___y_1256_,
                                    v___y_1257_,
                                    v___y_1258_,
                                    leanh::lean_box(0),
                                );
                                v___y_1261_ = v___x_1284_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_inc(v___y_1258_);
                            leanh::lean_inc_ref(v___y_1257_);
                            leanh::lean_inc(v___y_1256_);
                            leanh::lean_inc_ref(v___y_1255_);
                            v___x_1285_ = leanh::lean_apply_6(
                                v___f_1250_,
                                v_a_1280_,
                                v___y_1255_,
                                v___y_1256_,
                                v___y_1257_,
                                v___y_1258_,
                                leanh::lean_box(0),
                            );
                            v___y_1261_ = v___x_1285_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_1258_);
                        leanh::lean_dec_ref(v___y_1257_);
                        leanh::lean_dec(v___y_1256_);
                        leanh::lean_dec_ref(v___y_1255_);
                        leanh::lean_dec_ref(v___f_1250_);
                        v_a_1286_ = leanh::lean_ctor_get(v___x_1279_, 0);
                        v_isSharedCheck_1293_ =
                            (!leanh::lean_is_exclusive(v___x_1279_)) as u8;
                        if v_isSharedCheck_1293_ == 0 {
                            v___x_1288_ = v___x_1279_;
                            v_isShared_1289_ = v_isSharedCheck_1293_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1286_);
                            leanh::lean_dec(v___x_1279_);
                            v___x_1288_ = leanh::lean_box(0);
                            v_isShared_1289_ = v_isSharedCheck_1293_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1258_);
                    leanh::lean_dec_ref(v___y_1257_);
                    leanh::lean_dec(v___y_1256_);
                    leanh::lean_dec_ref(v___y_1255_);
                    leanh::lean_dec_ref(v___f_1250_);
                    v_a_1294_ = leanh::lean_ctor_get(v___x_1273_, 0);
                    v_isSharedCheck_1301_ = (!leanh::lean_is_exclusive(v___x_1273_)) as u8;
                    if v_isSharedCheck_1301_ == 0 {
                        v___x_1296_ = v___x_1273_;
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1294_);
                        leanh::lean_dec(v___x_1273_);
                        v___x_1296_ = leanh::lean_box(0);
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1261_) == 0 {
                    leanh::lean_dec_ref_known(v___y_1261_, 1);
                    v___x_1262_ = leanh::lean_box(0);
                    v___x_1263_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1262_,
                        v___y_1252_,
                        v___y_1255_,
                        v___y_1256_,
                        v___y_1257_,
                        v___y_1258_,
                    );
                    leanh::lean_dec(v___y_1258_);
                    leanh::lean_dec_ref(v___y_1257_);
                    leanh::lean_dec(v___y_1256_);
                    leanh::lean_dec_ref(v___y_1255_);
                    if leanh::lean_obj_tag(v___x_1263_) == 0 {
                        v_isSharedCheck_1271_ =
                            (!leanh::lean_is_exclusive(v___x_1263_)) as u8;
                        if v_isSharedCheck_1271_ == 0 {
                            v_unused_1272_ = leanh::lean_ctor_get(v___x_1263_, 0);
                            leanh::lean_dec(v_unused_1272_);
                            v___x_1265_ = v___x_1263_;
                            v_isShared_1266_ = v_isSharedCheck_1271_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1263_);
                            v___x_1265_ = leanh::lean_box(0);
                            v_isShared_1266_ = v_isSharedCheck_1271_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1263_;
                    }
                } else {
                    leanh::lean_dec(v___y_1258_);
                    leanh::lean_dec_ref(v___y_1257_);
                    leanh::lean_dec(v___y_1256_);
                    leanh::lean_dec_ref(v___y_1255_);
                    return v___y_1261_;
                }
            }
            2 => {
                v___x_1267_ = leanh::lean_box(0);
                if v_isShared_1266_ == 0 {
                    leanh::lean_ctor_set(v___x_1265_, 0, v___x_1267_);
                    v___x_1269_ = v___x_1265_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
                    v___x_1269_ = v_reuseFailAlloc_1270_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1269_;
            }
            4 => {
                if v_isShared_1289_ == 0 {
                    v___x_1291_ = v___x_1288_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
                    v___x_1291_ = v_reuseFailAlloc_1292_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1291_;
            }
            6 => {
                if v_isShared_1297_ == 0 {
                    v___x_1299_ = v___x_1296_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
                    v___x_1299_ = v_reuseFailAlloc_1300_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed(
    mut v___x_1302_: *mut leanh::LeanObject,
    mut v___f_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2214__boxed_1313_: u8 = 0;
    let mut v_res_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2214__boxed_1313_ = (leanh::lean_unbox(v___x_1302_) as u8);
    v_res_1314_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(
        v___x_2214__boxed_1313_,
        v___f_1303_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
        v___y_1308_,
        v___y_1309_,
        v___y_1310_,
        v___y_1311_,
    );
    leanh::lean_dec(v___y_1307_);
    leanh::lean_dec_ref(v___y_1306_);
    leanh::lean_dec(v___y_1305_);
    leanh::lean_dec_ref(v___y_1304_);
    return v_res_1314_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1318_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1;
    v___x_1319_ = l_Lean_MessageData_ofFormat(v___x_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(
    mut v___f_1320_: *mut leanh::LeanObject,
    mut v_stx_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    v_options_1331_ = leanh::lean_ctor_get(v___y_1328_, 2);
    v___x_1332_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
    v___x_1333_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(
        v_options_1331_,
        v___x_1332_,
    );
    if v___x_1333_ == 0 {
        let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1334_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_1320_,
            v___y_1322_,
            v___y_1323_,
            v___y_1324_,
            v___y_1325_,
            v___y_1326_,
            v___y_1327_,
            v___y_1328_,
            v___y_1329_,
        );
        return v___x_1334_;
    } else {
        let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1335_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once),
            _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2,
        );
        v___x_1336_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(
            v_stx_1321_,
            v___x_1335_,
            v___y_1322_,
            v___y_1323_,
            v___y_1324_,
            v___y_1325_,
            v___y_1326_,
            v___y_1327_,
            v___y_1328_,
            v___y_1329_,
        );
        if leanh::lean_obj_tag(v___x_1336_) == 0 {
            let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_1336_, 1);
            v___x_1337_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                v___f_1320_,
                v___y_1322_,
                v___y_1323_,
                v___y_1324_,
                v___y_1325_,
                v___y_1326_,
                v___y_1327_,
                v___y_1328_,
                v___y_1329_,
            );
            return v___x_1337_;
        } else {
            leanh::lean_dec_ref(v___f_1320_);
            return v___x_1336_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed(
    mut v___f_1338_: *mut leanh::LeanObject,
    mut v_stx_1339_: *mut leanh::LeanObject,
    mut v___y_1340_: *mut leanh::LeanObject,
    mut v___y_1341_: *mut leanh::LeanObject,
    mut v___y_1342_: *mut leanh::LeanObject,
    mut v___y_1343_: *mut leanh::LeanObject,
    mut v___y_1344_: *mut leanh::LeanObject,
    mut v___y_1345_: *mut leanh::LeanObject,
    mut v___y_1346_: *mut leanh::LeanObject,
    mut v___y_1347_: *mut leanh::LeanObject,
    mut v___y_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(
        v___f_1338_,
        v_stx_1339_,
        v___y_1340_,
        v___y_1341_,
        v___y_1342_,
        v___y_1343_,
        v___y_1344_,
        v___y_1345_,
        v___y_1346_,
        v___y_1347_,
    );
    leanh::lean_dec(v___y_1347_);
    leanh::lean_dec_ref(v___y_1346_);
    leanh::lean_dec(v___y_1345_);
    leanh::lean_dec_ref(v___y_1344_);
    leanh::lean_dec(v___y_1343_);
    leanh::lean_dec_ref(v___y_1342_);
    leanh::lean_dec(v___y_1341_);
    leanh::lean_dec_ref(v___y_1340_);
    leanh::lean_dec(v_stx_1339_);
    return v_res_1349_;
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv(
    mut v_stx_1357_: *mut leanh::LeanObject,
    mut v_a_1358_: *mut leanh::LeanObject,
    mut v_a_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
    mut v_a_1361_: *mut leanh::LeanObject,
    mut v_a_1362_: *mut leanh::LeanObject,
    mut v_a_1363_: *mut leanh::LeanObject,
    mut v_a_1364_: *mut leanh::LeanObject,
    mut v_a_1365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    v___x_1367_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1;
    leanh::lean_inc(v_stx_1357_);
    v___x_1368_ = l_Lean_Syntax_isOfKind(v_stx_1357_, v___x_1367_);
    if v___x_1368_ == 0 {
        let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_1357_);
        v___x_1369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg();
        return v___x_1369_;
    } else {
        let mut v___f_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1370_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2;
        v___x_1371_ = leanh::lean_box((v___x_1368_) as usize);
        v___f_1372_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed as *mut core::ffi::c_void,
            11,
            2,
        );
        leanh::lean_closure_set(v___f_1372_, 0, v___x_1371_);
        leanh::lean_closure_set(v___f_1372_, 1, v___f_1370_);
        v___f_1373_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed as *mut core::ffi::c_void,
            11,
            2,
        );
        leanh::lean_closure_set(v___f_1373_, 0, v___f_1372_);
        leanh::lean_closure_set(v___f_1373_, 1, v_stx_1357_);
        v___x_1374_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_1373_,
            v_a_1358_,
            v_a_1359_,
            v_a_1360_,
            v_a_1361_,
            v_a_1362_,
            v_a_1363_,
            v_a_1364_,
            v_a_1365_,
        );
        return v___x_1374_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(
    mut v_stx_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
    mut v_a_1377_: *mut leanh::LeanObject,
    mut v_a_1378_: *mut leanh::LeanObject,
    mut v_a_1379_: *mut leanh::LeanObject,
    mut v_a_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv(
        v_stx_1375_,
        v_a_1376_,
        v_a_1377_,
        v_a_1378_,
        v_a_1379_,
        v_a_1380_,
        v_a_1381_,
        v_a_1382_,
        v_a_1383_,
    );
    leanh::lean_dec(v_a_1383_);
    leanh::lean_dec_ref(v_a_1382_);
    leanh::lean_dec(v_a_1381_);
    leanh::lean_dec_ref(v_a_1380_);
    leanh::lean_dec(v_a_1379_);
    leanh::lean_dec_ref(v_a_1378_);
    leanh::lean_dec(v_a_1377_);
    leanh::lean_dec_ref(v_a_1376_);
    return v_res_1385_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(
    mut v_00_u03b1_1386_: *mut leanh::LeanObject,
    mut v_msg_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
    mut v___y_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(
        v_msg_1387_,
        v___y_1388_,
        v___y_1389_,
        v___y_1390_,
        v___y_1391_,
    );
    return v___x_1393_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(
    mut v_00_u03b1_1394_: *mut leanh::LeanObject,
    mut v_msg_1395_: *mut leanh::LeanObject,
    mut v___y_1396_: *mut leanh::LeanObject,
    mut v___y_1397_: *mut leanh::LeanObject,
    mut v___y_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(
        v_00_u03b1_1394_,
        v_msg_1395_,
        v___y_1396_,
        v___y_1397_,
        v___y_1398_,
        v___y_1399_,
    );
    leanh::lean_dec(v___y_1399_);
    leanh::lean_dec_ref(v___y_1398_);
    leanh::lean_dec(v___y_1397_);
    leanh::lean_dec_ref(v___y_1396_);
    return v_res_1401_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1()
-> *mut leanh::LeanObject {
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1411_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1;
    v___x_1412_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1;
    v___x_1413_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1410_,
        v___x_1411_,
        v___x_1412_,
        v___x_1413_,
    );
    return v___x_1414_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(
    mut v_a_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
    return v_res_1416_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Cbv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Cbv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Cbv(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Cbv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Cbv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Cbv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Cbv(builtin);
}