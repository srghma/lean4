// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Eqns
// Imports: Lean.Elab.PreDefinition.FixedParams Lean.Meta.ArgsPacker.Basic
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_float_decLt, lean_float_div, lean_float_sub,
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now, lean_mk_empty_array_with_capacity,
    lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_hasValue;
use crate::r#gen::Lean::Elab::DefView::l_Lean_Elab_DefKind_isTheorem;
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    initialize_Lean_Elab_PreDefinition_FixedParams,
    l_Lean_Elab_instInhabitedFixedParamPerms_default,
    runtime_initialize_Lean_Elab_PreDefinition_FixedParams,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_allImportedModuleNames, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::ArgsPacker::Basic::{
    initialize_Lean_Meta_ArgsPacker_Basic, l_Lean_Meta_instInhabitedArgsPacker_default,
    runtime_initialize_Lean_Meta_ArgsPacker_Basic,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_realizeConst;
use crate::r#gen::Lean::Meta::Eqns::{
    l_Lean_Meta_ensureEqnReservedNamesAvailable, l_Lean_Meta_mkEqLikeNameFor,
    l_Lean_Meta_registerGetUnfoldEqnFn, l_Lean_Meta_unfoldThmSuffix,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::PrivateName::{
    l_Lean_isPrivateName, l_Lean_mkPrivateNameCore, l_Lean_privateToUserName,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
pub static l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__3_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_WF_instInhabitedEqnInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_WF_instInhabitedEqnInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [87, 70, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 113, 110, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15475474165463193880 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4976684976444472913 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_WF_eqnInfoExt: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_WF_registerEqnsInfo___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [99, 111, 112, 121, 80, 114, 105, 118, 97, 116, 101, 85, 110, 102, 111, 108, 100, 84, 104, 101, 111, 114, 101, 109, 32, 114, 117, 110, 110, 105, 110, 103, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__3_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__5: f64 = 0.0;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__2___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__1_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [82, 101, 115, 101, 114, 118, 101, 100, 78, 97, 109, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__1_value) as *mut leanh::LeanObject,16524425170056508783 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__3_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__4_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__7: f64 = 0.0;
pub unsafe fn _init_l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = leanh::lean_box(0);
    v___x_1692_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__1;
    v___x_1693_ = l_Lean_Expr_const___override(v___x_1692_, v___x_1691_);
    return v___x_1693_;
}
pub unsafe fn _init_l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
    v___x_1697_ = l_Lean_Meta_instInhabitedArgsPacker_default;
    v___x_1698_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__3;
    v___x_1699_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__2_once),
        _init_l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__2,
    );
    v___x_1700_ = leanh::lean_box(0);
    v___x_1701_ = leanh::lean_box(0);
    v___x_1702_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_1702_, 0, v___x_1701_);
    leanh::lean_ctor_set(v___x_1702_, 1, v___x_1700_);
    leanh::lean_ctor_set(v___x_1702_, 2, v___x_1699_);
    leanh::lean_ctor_set(v___x_1702_, 3, v___x_1699_);
    leanh::lean_ctor_set(v___x_1702_, 4, v___x_1698_);
    leanh::lean_ctor_set(v___x_1702_, 5, v___x_1701_);
    leanh::lean_ctor_set(v___x_1702_, 6, v___x_1697_);
    leanh::lean_ctor_set(v___x_1702_, 7, v___x_1696_);
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_Elab_WF_instInhabitedEqnInfo_default() -> *mut leanh::LeanObject {
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__4_once),
        _init_l_Lean_Elab_WF_instInhabitedEqnInfo_default___closed__4,
    );
    return v___x_1703_;
}
pub unsafe fn _init_l_Lean_Elab_WF_instInhabitedEqnInfo() -> *mut leanh::LeanObject {
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
    return v___x_1704_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_(
    mut v_env_1705_: *mut leanh::LeanObject,
    mut v_n_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = 1;
    v___x_1709_ = l_Lean_Environment_setExporting(v_env_1705_, v___x_1708_);
    v___x_1710_ = 0;
    v___x_1711_ = l_Lean_Environment_find_x3f(v___x_1709_, v_n_1706_, v___x_1710_);
    if leanh::lean_obj_tag(v___x_1711_) == 0 {
        return v___x_1710_;
    } else {
        let mut v_val_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: u8 = 0;
        v_val_1712_ = leanh::lean_ctor_get(v___x_1711_, 0);
        leanh::lean_inc(v_val_1712_);
        leanh::lean_dec_ref_known(v___x_1711_, 1);
        v___x_1713_ = l_Lean_ConstantInfo_hasValue(v_val_1712_, v___x_1710_);
        leanh::lean_dec(v_val_1712_);
        return v___x_1713_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2____boxed(
    mut v_env_1714_: *mut leanh::LeanObject,
    mut v_n_1715_: *mut leanh::LeanObject,
    mut v_x_1716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1717_: u8 = 0;
    let mut v_r_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1717_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_(v_env_1714_, v_n_1715_, v_x_1716_);
    leanh::lean_dec_ref(v_x_1716_);
    v_r_1718_ = leanh::lean_box((v_res_1717_) as usize);
    return v_r_1718_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_1719_: *mut leanh::LeanObject,
    mut v_x_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1720_) == 0 {
                    v_k_1721_ = leanh::lean_ctor_get(v_x_1720_, 1);
                    v_v_1722_ = leanh::lean_ctor_get(v_x_1720_, 2);
                    v_l_1723_ = leanh::lean_ctor_get(v_x_1720_, 3);
                    v_r_1724_ = leanh::lean_ctor_get(v_x_1720_, 4);
                    v___x_1725_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_1719_, v_l_1723_);
                    leanh::lean_inc(v_v_1722_);
                    leanh::lean_inc(v_k_1721_);
                    v___x_1726_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1726_, 0, v_k_1721_);
                    leanh::lean_ctor_set(v___x_1726_, 1, v_v_1722_);
                    v___x_1727_ = lean_array_push(v___x_1725_, v___x_1726_);
                    v_init_1719_ = v___x_1727_;
                    v_x_1720_ = v_r_1724_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1719_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_1729_: *mut leanh::LeanObject,
    mut v_x_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_1729_, v_x_1730_);
    leanh::lean_dec(v_x_1730_);
    return v_res_1731_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_(
    mut v_env_1734_: *mut leanh::LeanObject,
    mut v_s_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1736_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___f_1736_, 0, v_env_1734_);
    v___x_1737_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_;
    v_all_1738_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_1737_, v_s_1735_);
    v___x_1739_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
        v___f_1736_,
        v_s_1735_,
    );
    v_exported_1740_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_1737_, v___x_1739_);
    leanh::lean_dec(v___x_1739_);
    leanh::lean_inc_ref(v_exported_1740_);
    v___x_1741_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1741_, 0, v_exported_1740_);
    leanh::lean_ctor_set(v___x_1741_, 1, v_exported_1740_);
    leanh::lean_ctor_set(v___x_1741_, 2, v_all_1738_);
    return v___x_1741_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1755_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_1756_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_1757_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_1758_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1756_, v___x_1757_, v___f_1755_);
    return v___x_1758_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2____boxed(
    mut v_a_1759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1760_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_();
    return v_res_1760_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0(
    mut v_init_1761_: *mut leanh::LeanObject,
    mut v_t_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_1761_, v_t_1762_);
    return v___x_1763_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_1764_: *mut leanh::LeanObject,
    mut v_t_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2__spec__0(v_init_1764_, v_t_1765_);
    leanh::lean_dec(v_t_1765_);
    return v_res_1766_;
}
pub unsafe fn l_Lean_Elab_WF_registerEqnsInfo___lam__0(
    mut v___x_1767_: u8,
    mut v___x_1768_: u8,
    mut v_____do__lift_1769_: u8,
    mut v___y_1770_: *mut leanh::LeanObject,
    mut v___y_1771_: *mut leanh::LeanObject,
    mut v___y_1772_: *mut leanh::LeanObject,
    mut v___y_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1769_ == 0 {
        let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1775_ = leanh::lean_box((v___x_1767_) as usize);
        v___x_1776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1776_, 0, v___x_1775_);
        return v___x_1776_;
    } else {
        let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1777_ = leanh::lean_box((v___x_1768_) as usize);
        v___x_1778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
        return v___x_1778_;
    }
}
pub unsafe fn l_Lean_Elab_WF_registerEqnsInfo___lam__0___boxed(
    mut v___x_1779_: *mut leanh::LeanObject,
    mut v___x_1780_: *mut leanh::LeanObject,
    mut v_____do__lift_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4040__boxed_1787_: u8 = 0;
    let mut v___x_4041__boxed_1788_: u8 = 0;
    let mut v_____do__lift_4042__boxed_1789_: u8 = 0;
    let mut v_res_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4040__boxed_1787_ = (leanh::lean_unbox(v___x_1779_) as u8);
    v___x_4041__boxed_1788_ = (leanh::lean_unbox(v___x_1780_) as u8);
    v_____do__lift_4042__boxed_1789_ = (leanh::lean_unbox(v_____do__lift_1781_) as u8);
    v_res_1790_ = l_Lean_Elab_WF_registerEqnsInfo___lam__0(
        v___x_4040__boxed_1787_,
        v___x_4041__boxed_1788_,
        v_____do__lift_4042__boxed_1789_,
        v___y_1782_,
        v___y_1783_,
        v___y_1784_,
        v___y_1785_,
    );
    leanh::lean_dec(v___y_1785_);
    leanh::lean_dec_ref(v___y_1784_);
    leanh::lean_dec(v___y_1783_);
    leanh::lean_dec_ref(v___y_1782_);
    return v_res_1790_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_registerEqnsInfo_spec__0(
    mut v_sz_1791_: usize,
    mut v_i_1792_: usize,
    mut v_bs_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1794_: u8 = 0;
    let mut v_v_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: usize = 0;
    let mut v___x_1800_: usize = 0;
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1794_ = lean_usize_dec_lt(v_i_1792_, v_sz_1791_);
                if v___x_1794_ == 0 {
                    return v_bs_1793_;
                } else {
                    v_v_1795_ = lean_array_uget_borrowed(v_bs_1793_, v_i_1792_);
                    v_declName_1796_ = leanh::lean_ctor_get(v_v_1795_, 3);
                    leanh::lean_inc(v_declName_1796_);
                    v___x_1797_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1798_ = lean_array_uset(v_bs_1793_, v_i_1792_, v___x_1797_);
                    v___x_1799_ = 1usize;
                    v___x_1800_ = lean_usize_add(v_i_1792_, v___x_1799_);
                    v___x_1801_ = lean_array_uset(v_bs_x27_1798_, v_i_1792_, v_declName_1796_);
                    v_i_1792_ = v___x_1800_;
                    v_bs_1793_ = v___x_1801_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_registerEqnsInfo_spec__0___boxed(
    mut v_sz_1803_: *mut leanh::LeanObject,
    mut v_i_1804_: *mut leanh::LeanObject,
    mut v_bs_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1806_: usize = 0;
    let mut v_i_boxed_1807_: usize = 0;
    let mut v_res_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1806_ = leanh::lean_unbox_usize(v_sz_1803_);
    leanh::lean_dec(v_sz_1803_);
    v_i_boxed_1807_ = leanh::lean_unbox_usize(v_i_1804_);
    leanh::lean_dec(v_i_1804_);
    v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_registerEqnsInfo_spec__0(v_sz_boxed_1806_, v_i_boxed_1807_, v_bs_1805_);
    return v_res_1808_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4___redArg(
    mut v_as_1809_: *mut leanh::LeanObject,
    mut v_i_1810_: usize,
    mut v_stop_1811_: usize,
    mut v_b_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: usize = 0;
    let mut v___x_1822_: usize = 0;
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1816_ = lean_usize_dec_eq(v_i_1810_, v_stop_1811_);
                if v___x_1816_ == 0 {
                    v___x_1817_ = lean_array_uget_borrowed(v_as_1809_, v_i_1810_);
                    v_declName_1818_ = leanh::lean_ctor_get(v___x_1817_, 3);
                    leanh::lean_inc(v_declName_1818_);
                    v___x_1819_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(
                        v_declName_1818_,
                        v___y_1813_,
                        v___y_1814_,
                    );
                    if leanh::lean_obj_tag(v___x_1819_) == 0 {
                        v_a_1820_ = leanh::lean_ctor_get(v___x_1819_, 0);
                        leanh::lean_inc(v_a_1820_);
                        leanh::lean_dec_ref_known(v___x_1819_, 1);
                        v___x_1821_ = 1usize;
                        v___x_1822_ = lean_usize_add(v_i_1810_, v___x_1821_);
                        v_i_1810_ = v___x_1822_;
                        v_b_1812_ = v_a_1820_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1819_;
                    }
                } else {
                    v___x_1824_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1824_, 0, v_b_1812_);
                    return v___x_1824_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4___redArg___boxed(
    mut v_as_1825_: *mut leanh::LeanObject,
    mut v_i_1826_: *mut leanh::LeanObject,
    mut v_stop_1827_: *mut leanh::LeanObject,
    mut v_b_1828_: *mut leanh::LeanObject,
    mut v___y_1829_: *mut leanh::LeanObject,
    mut v___y_1830_: *mut leanh::LeanObject,
    mut v___y_1831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1832_: usize = 0;
    let mut v_stop_boxed_1833_: usize = 0;
    let mut v_res_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1832_ = leanh::lean_unbox_usize(v_i_1826_);
    leanh::lean_dec(v_i_1826_);
    v_stop_boxed_1833_ = leanh::lean_unbox_usize(v_stop_1827_);
    leanh::lean_dec(v_stop_1827_);
    v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4___redArg(v_as_1825_, v_i_boxed_1832_, v_stop_boxed_1833_, v_b_1828_, v___y_1829_, v___y_1830_);
    leanh::lean_dec(v___y_1830_);
    leanh::lean_dec_ref(v___y_1829_);
    leanh::lean_dec_ref(v_as_1825_);
    return v_res_1834_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__3(
    mut v___x_1835_: u8,
    mut v_as_1836_: *mut leanh::LeanObject,
    mut v_i_1837_: usize,
    mut v_stop_1838_: usize,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1845_: usize = 0;
    let mut v___x_1846_: usize = 0;
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v_a_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: u8 = 0;
    let mut v_a_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1848_ = lean_usize_dec_eq(v_i_1837_, v_stop_1838_);
                if v___x_1848_ == 0 {
                    v___x_1849_ = lean_array_uget_borrowed(v_as_1836_, v_i_1837_);
                    v_type_1850_ = leanh::lean_ctor_get(v___x_1849_, 6);
                    v___x_1851_ = 1;
                    leanh::lean_inc_ref(v_type_1850_);
                    v___x_1856_ = l_Lean_Meta_isProp(
                        v_type_1850_,
                        v___y_1839_,
                        v___y_1840_,
                        v___y_1841_,
                        v___y_1842_,
                    );
                    if leanh::lean_obj_tag(v___x_1856_) == 0 {
                        v_a_1857_ = leanh::lean_ctor_get(v___x_1856_, 0);
                        leanh::lean_inc(v_a_1857_);
                        leanh::lean_dec_ref_known(v___x_1856_, 1);
                        v___x_1858_ = (leanh::lean_unbox(v_a_1857_) as u8);
                        leanh::lean_dec(v_a_1857_);
                        if v___x_1858_ == 0 {
                            v_a_1853_ = v___x_1835_;
                            state = 2;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1856_) == 0 {
                            v_a_1859_ = leanh::lean_ctor_get(v___x_1856_, 0);
                            leanh::lean_inc(v_a_1859_);
                            leanh::lean_dec_ref_known(v___x_1856_, 1);
                            v___x_1860_ = (leanh::lean_unbox(v_a_1859_) as u8);
                            leanh::lean_dec(v_a_1859_);
                            v_a_1853_ = v___x_1860_;
                            state = 2;
                            continue;
                        } else {
                            return v___x_1856_;
                        }
                    }
                } else {
                    v___x_1861_ = 0;
                    v___x_1862_ = leanh::lean_box((v___x_1861_) as usize);
                    v___x_1863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
                    return v___x_1863_;
                }
            }
            1 => {
                v___x_1845_ = 1usize;
                v___x_1846_ = lean_usize_add(v_i_1837_, v___x_1845_);
                v_i_1837_ = v___x_1846_;
                state = 0;
                continue;
            }
            2 => {
                if v_a_1853_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1854_ = leanh::lean_box((v___x_1851_) as usize);
                    v___x_1855_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1855_, 0, v___x_1854_);
                    return v___x_1855_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__3___boxed(
    mut v___x_1864_: *mut leanh::LeanObject,
    mut v_as_1865_: *mut leanh::LeanObject,
    mut v_i_1866_: *mut leanh::LeanObject,
    mut v_stop_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
    mut v___y_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
    mut v___y_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4110__boxed_1873_: u8 = 0;
    let mut v_i_boxed_1874_: usize = 0;
    let mut v_stop_boxed_1875_: usize = 0;
    let mut v_res_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4110__boxed_1873_ = (leanh::lean_unbox(v___x_1864_) as u8);
    v_i_boxed_1874_ = leanh::lean_unbox_usize(v_i_1866_);
    leanh::lean_dec(v_i_1866_);
    v_stop_boxed_1875_ = leanh::lean_unbox_usize(v_stop_1867_);
    leanh::lean_dec(v_stop_1867_);
    v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__3(v___x_4110__boxed_1873_, v_as_1865_, v_i_boxed_1874_, v_stop_boxed_1875_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
    leanh::lean_dec(v___y_1871_);
    leanh::lean_dec_ref(v___y_1870_);
    leanh::lean_dec(v___y_1869_);
    leanh::lean_dec_ref(v___y_1868_);
    leanh::lean_dec_ref(v_as_1865_);
    return v_res_1876_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__2(
    mut v_as_1877_: *mut leanh::LeanObject,
    mut v_i_1878_: usize,
    mut v_stop_1879_: usize,
) -> u8 {
    let mut v___x_1880_: u8 = 0;
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1882_: u8 = 0;
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: u8 = 0;
    let mut v___x_1885_: usize = 0;
    let mut v___x_1886_: usize = 0;
    let mut v___x_1888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = lean_usize_dec_eq(v_i_1878_, v_stop_1879_);
                if v___x_1880_ == 0 {
                    v___x_1881_ = lean_array_uget_borrowed(v_as_1877_, v_i_1878_);
                    v_kind_1882_ = leanh::lean_ctor_get_uint8(
                        v___x_1881_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                    );
                    v___x_1883_ = 1;
                    v___x_1884_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1882_);
                    if v___x_1884_ == 0 {
                        return v___x_1883_;
                    } else {
                        if v___x_1880_ == 0 {
                            v___x_1885_ = 1usize;
                            v___x_1886_ = lean_usize_add(v_i_1878_, v___x_1885_);
                            v_i_1878_ = v___x_1886_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1883_;
                        }
                    }
                } else {
                    v___x_1888_ = 0;
                    return v___x_1888_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__2___boxed(
    mut v_as_1889_: *mut leanh::LeanObject,
    mut v_i_1890_: *mut leanh::LeanObject,
    mut v_stop_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1892_: usize = 0;
    let mut v_stop_boxed_1893_: usize = 0;
    let mut v_res_1894_: u8 = 0;
    let mut v_r_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1892_ = leanh::lean_unbox_usize(v_i_1890_);
    leanh::lean_dec(v_i_1890_);
    v_stop_boxed_1893_ = leanh::lean_unbox_usize(v_stop_1891_);
    leanh::lean_dec(v_stop_1891_);
    v_res_1894_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__2(v_as_1889_, v_i_boxed_1892_, v_stop_boxed_1893_);
    leanh::lean_dec_ref(v_as_1889_);
    v_r_1895_ = leanh::lean_box((v_res_1894_) as usize);
    return v_r_1895_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__1(
    mut v___x_1896_: *mut leanh::LeanObject,
    mut v_declNameNonRec_1897_: *mut leanh::LeanObject,
    mut v_argsPacker_1898_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_1899_: *mut leanh::LeanObject,
    mut v_as_1900_: *mut leanh::LeanObject,
    mut v_i_1901_: usize,
    mut v_stop_1902_: usize,
    mut v_b_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: usize = 0;
    let mut v___x_1914_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1904_ = lean_usize_dec_eq(v_i_1901_, v_stop_1902_);
                if v___x_1904_ == 0 {
                    v___x_1905_ = lean_array_uget_borrowed(v_as_1900_, v_i_1901_);
                    v_levelParams_1906_ = leanh::lean_ctor_get(v___x_1905_, 1);
                    v_declName_1907_ = leanh::lean_ctor_get(v___x_1905_, 3);
                    v_type_1908_ = leanh::lean_ctor_get(v___x_1905_, 6);
                    v_value_1909_ = leanh::lean_ctor_get(v___x_1905_, 7);
                    v___x_1910_ = l_Lean_Elab_WF_eqnInfoExt;
                    leanh::lean_inc_ref(v_fixedParamPerms_1899_);
                    leanh::lean_inc_ref(v_argsPacker_1898_);
                    leanh::lean_inc(v_declNameNonRec_1897_);
                    leanh::lean_inc_ref(v___x_1896_);
                    leanh::lean_inc_ref(v_value_1909_);
                    leanh::lean_inc_ref(v_type_1908_);
                    leanh::lean_inc(v_levelParams_1906_);
                    leanh::lean_inc_n(v_declName_1907_, 2);
                    v___x_1911_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v___x_1911_, 0, v_declName_1907_);
                    leanh::lean_ctor_set(v___x_1911_, 1, v_levelParams_1906_);
                    leanh::lean_ctor_set(v___x_1911_, 2, v_type_1908_);
                    leanh::lean_ctor_set(v___x_1911_, 3, v_value_1909_);
                    leanh::lean_ctor_set(v___x_1911_, 4, v___x_1896_);
                    leanh::lean_ctor_set(v___x_1911_, 5, v_declNameNonRec_1897_);
                    leanh::lean_ctor_set(v___x_1911_, 6, v_argsPacker_1898_);
                    leanh::lean_ctor_set(v___x_1911_, 7, v_fixedParamPerms_1899_);
                    v___x_1912_ = l_Lean_MapDeclarationExtension_insert___redArg(
                        v___x_1910_,
                        v_b_1903_,
                        v_declName_1907_,
                        v___x_1911_,
                    );
                    v___x_1913_ = 1usize;
                    v___x_1914_ = lean_usize_add(v_i_1901_, v___x_1913_);
                    v_i_1901_ = v___x_1914_;
                    v_b_1903_ = v___x_1912_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_fixedParamPerms_1899_);
                    leanh::lean_dec_ref(v_argsPacker_1898_);
                    leanh::lean_dec(v_declNameNonRec_1897_);
                    leanh::lean_dec_ref(v___x_1896_);
                    return v_b_1903_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__1___boxed(
    mut v___x_1916_: *mut leanh::LeanObject,
    mut v_declNameNonRec_1917_: *mut leanh::LeanObject,
    mut v_argsPacker_1918_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_1919_: *mut leanh::LeanObject,
    mut v_as_1920_: *mut leanh::LeanObject,
    mut v_i_1921_: *mut leanh::LeanObject,
    mut v_stop_1922_: *mut leanh::LeanObject,
    mut v_b_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1924_: usize = 0;
    let mut v_stop_boxed_1925_: usize = 0;
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1924_ = leanh::lean_unbox_usize(v_i_1921_);
    leanh::lean_dec(v_i_1921_);
    v_stop_boxed_1925_ = leanh::lean_unbox_usize(v_stop_1922_);
    leanh::lean_dec(v_stop_1922_);
    v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__1(v___x_1916_, v_declNameNonRec_1917_, v_argsPacker_1918_, v_fixedParamPerms_1919_, v_as_1920_, v_i_boxed_1924_, v_stop_boxed_1925_, v_b_1923_);
    leanh::lean_dec_ref(v_as_1920_);
    return v_res_1926_;
}
pub unsafe fn _init_l_Lean_Elab_WF_registerEqnsInfo___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1927_;
}
pub unsafe fn _init_l_Lean_Elab_WF_registerEqnsInfo___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__0_once),
        _init_l_Lean_Elab_WF_registerEqnsInfo___closed__0,
    );
    v___x_1929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1929_, 0, v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn _init_l_Lean_Elab_WF_registerEqnsInfo___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__1_once),
        _init_l_Lean_Elab_WF_registerEqnsInfo___closed__1,
    );
    v___x_1931_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1931_, 0, v___x_1930_);
    leanh::lean_ctor_set(v___x_1931_, 1, v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lean_Elab_WF_registerEqnsInfo___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__1_once),
        _init_l_Lean_Elab_WF_registerEqnsInfo___closed__1,
    );
    v___x_1933_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1932_);
    leanh::lean_ctor_set(v___x_1933_, 1, v___x_1932_);
    leanh::lean_ctor_set(v___x_1933_, 2, v___x_1932_);
    leanh::lean_ctor_set(v___x_1933_, 3, v___x_1932_);
    leanh::lean_ctor_set(v___x_1933_, 4, v___x_1932_);
    leanh::lean_ctor_set(v___x_1933_, 5, v___x_1932_);
    return v___x_1933_;
}
pub unsafe fn l_Lean_Elab_WF_registerEqnsInfo(
    mut v_preDefs_1934_: *mut leanh::LeanObject,
    mut v_declNameNonRec_1935_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_1936_: *mut leanh::LeanObject,
    mut v_argsPacker_1937_: *mut leanh::LeanObject,
    mut v_a_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1965_: u8 = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_unused_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v_sz_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: usize = 0;
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: usize = 0;
    let mut v___x_2013_: usize = 0;
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: usize = 0;
    let mut v___x_2027_: usize = 0;
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: usize = 0;
    let mut v___x_2030_: usize = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1978_ = leanh::lean_unsigned_to_nat(0);
                v___x_1979_ = lean_array_get_size(v_preDefs_1934_);
                v___x_2023_ = lean_nat_dec_lt(v___x_1978_, v___x_1979_);
                if v___x_2023_ == 0 {
                    state = 9;
                    continue;
                } else {
                    v___x_2024_ = leanh::lean_box(0);
                    v___x_2025_ = lean_nat_dec_le(v___x_1979_, v___x_1979_);
                    if v___x_2025_ == 0 {
                        if v___x_2023_ == 0 {
                            state = 9;
                            continue;
                        } else {
                            v___x_2026_ = 0usize;
                            v___x_2027_ = lean_usize_of_nat(v___x_1979_);
                            v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4___redArg(v_preDefs_1934_, v___x_2026_, v___x_2027_, v___x_2024_, v_a_1940_, v_a_1941_);
                            v___y_2022_ = v___x_2028_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_2029_ = 0usize;
                        v___x_2030_ = lean_usize_of_nat(v___x_1979_);
                        v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4___redArg(v_preDefs_1934_, v___x_2029_, v___x_2030_, v___x_2024_, v_a_1940_, v_a_1941_);
                        v___y_2022_ = v___x_2031_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1944_ = leanh::lean_box(0);
                v___x_1945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1945_, 0, v___x_1944_);
                return v___x_1945_;
            }
            2 => {
                v___x_1955_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__2_once),
                    _init_l_Lean_Elab_WF_registerEqnsInfo___closed__2,
                );
                v___x_1956_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_1956_, 0, v___y_1954_);
                leanh::lean_ctor_set(v___x_1956_, 1, v_nextMacroScope_1947_);
                leanh::lean_ctor_set(v___x_1956_, 2, v_ngen_1948_);
                leanh::lean_ctor_set(v___x_1956_, 3, v_auxDeclNGen_1949_);
                leanh::lean_ctor_set(v___x_1956_, 4, v_traceState_1950_);
                leanh::lean_ctor_set(v___x_1956_, 5, v___x_1955_);
                leanh::lean_ctor_set(v___x_1956_, 6, v_messages_1951_);
                leanh::lean_ctor_set(v___x_1956_, 7, v_infoState_1952_);
                leanh::lean_ctor_set(v___x_1956_, 8, v_snapshotTasks_1953_);
                v___x_1957_ = lean_st_ref_set(v_a_1941_, v___x_1956_);
                v___x_1958_ = lean_st_ref_take(v_a_1939_);
                v_mctx_1959_ = leanh::lean_ctor_get(v___x_1958_, 0);
                v_zetaDeltaFVarIds_1960_ = leanh::lean_ctor_get(v___x_1958_, 2);
                v_postponed_1961_ = leanh::lean_ctor_get(v___x_1958_, 3);
                v_diag_1962_ = leanh::lean_ctor_get(v___x_1958_, 4);
                v_isSharedCheck_1973_ = (!leanh::lean_is_exclusive(v___x_1958_)) as u8;
                if v_isSharedCheck_1973_ == 0 {
                    v_unused_1974_ = leanh::lean_ctor_get(v___x_1958_, 1);
                    leanh::lean_dec(v_unused_1974_);
                    v___x_1964_ = v___x_1958_;
                    v_isShared_1965_ = v_isSharedCheck_1973_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1962_);
                    leanh::lean_inc(v_postponed_1961_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1960_);
                    leanh::lean_inc(v_mctx_1959_);
                    leanh::lean_dec(v___x_1958_);
                    v___x_1964_ = leanh::lean_box(0);
                    v_isShared_1965_ = v_isSharedCheck_1973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1966_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_registerEqnsInfo___closed__3_once),
                    _init_l_Lean_Elab_WF_registerEqnsInfo___closed__3,
                );
                if v_isShared_1965_ == 0 {
                    leanh::lean_ctor_set(v___x_1964_, 1, v___x_1966_);
                    v___x_1968_ = v___x_1964_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_mctx_1959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1966_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1972_,
                        2,
                        v_zetaDeltaFVarIds_1960_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_postponed_1961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_diag_1962_);
                    v___x_1968_ = v_reuseFailAlloc_1972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1969_ = lean_st_ref_set(v_a_1939_, v___x_1968_);
                v___x_1970_ = leanh::lean_box(0);
                v___x_1971_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1971_, 0, v___x_1970_);
                return v___x_1971_;
            }
            5 => {
                v___x_1976_ = leanh::lean_box(0);
                v___x_1977_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1977_, 0, v___x_1976_);
                return v___x_1977_;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_1981_) == 0 {
                    v_a_1982_ = leanh::lean_ctor_get(v___y_1981_, 0);
                    leanh::lean_inc(v_a_1982_);
                    leanh::lean_dec_ref_known(v___y_1981_, 1);
                    v___x_1983_ = (leanh::lean_unbox(v_a_1982_) as u8);
                    leanh::lean_dec(v_a_1982_);
                    if v___x_1983_ == 0 {
                        v___x_1984_ = lean_st_ref_take(v_a_1941_);
                        v_env_1985_ = leanh::lean_ctor_get(v___x_1984_, 0);
                        leanh::lean_inc_ref(v_env_1985_);
                        v_nextMacroScope_1986_ = leanh::lean_ctor_get(v___x_1984_, 1);
                        leanh::lean_inc(v_nextMacroScope_1986_);
                        v_ngen_1987_ = leanh::lean_ctor_get(v___x_1984_, 2);
                        leanh::lean_inc_ref(v_ngen_1987_);
                        v_auxDeclNGen_1988_ = leanh::lean_ctor_get(v___x_1984_, 3);
                        leanh::lean_inc_ref(v_auxDeclNGen_1988_);
                        v_traceState_1989_ = leanh::lean_ctor_get(v___x_1984_, 4);
                        leanh::lean_inc_ref(v_traceState_1989_);
                        v_messages_1990_ = leanh::lean_ctor_get(v___x_1984_, 6);
                        leanh::lean_inc_ref(v_messages_1990_);
                        v_infoState_1991_ = leanh::lean_ctor_get(v___x_1984_, 7);
                        leanh::lean_inc_ref(v_infoState_1991_);
                        v_snapshotTasks_1992_ = leanh::lean_ctor_get(v___x_1984_, 8);
                        leanh::lean_inc_ref(v_snapshotTasks_1992_);
                        leanh::lean_dec(v___x_1984_);
                        v___x_1993_ = lean_nat_dec_lt(v___x_1978_, v___x_1979_);
                        if v___x_1993_ == 0 {
                            leanh::lean_dec_ref(v_argsPacker_1937_);
                            leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                            leanh::lean_dec(v_declNameNonRec_1935_);
                            leanh::lean_dec_ref(v_preDefs_1934_);
                            v_nextMacroScope_1947_ = v_nextMacroScope_1986_;
                            v_ngen_1948_ = v_ngen_1987_;
                            v_auxDeclNGen_1949_ = v_auxDeclNGen_1988_;
                            v_traceState_1950_ = v_traceState_1989_;
                            v_messages_1951_ = v_messages_1990_;
                            v_infoState_1952_ = v_infoState_1991_;
                            v_snapshotTasks_1953_ = v_snapshotTasks_1992_;
                            v___y_1954_ = v_env_1985_;
                            state = 2;
                            continue;
                        } else {
                            v_sz_1994_ = lean_array_size(v_preDefs_1934_);
                            v___x_1995_ = 0usize;
                            leanh::lean_inc_ref(v_preDefs_1934_);
                            v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_registerEqnsInfo_spec__0(v_sz_1994_, v___x_1995_, v_preDefs_1934_);
                            v___x_1997_ = lean_nat_dec_le(v___x_1979_, v___x_1979_);
                            if v___x_1997_ == 0 {
                                if v___x_1993_ == 0 {
                                    leanh::lean_dec_ref(v___x_1996_);
                                    leanh::lean_dec_ref(v_argsPacker_1937_);
                                    leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                                    leanh::lean_dec(v_declNameNonRec_1935_);
                                    leanh::lean_dec_ref(v_preDefs_1934_);
                                    v_nextMacroScope_1947_ = v_nextMacroScope_1986_;
                                    v_ngen_1948_ = v_ngen_1987_;
                                    v_auxDeclNGen_1949_ = v_auxDeclNGen_1988_;
                                    v_traceState_1950_ = v_traceState_1989_;
                                    v_messages_1951_ = v_messages_1990_;
                                    v_infoState_1952_ = v_infoState_1991_;
                                    v_snapshotTasks_1953_ = v_snapshotTasks_1992_;
                                    v___y_1954_ = v_env_1985_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1998_ = lean_usize_of_nat(v___x_1979_);
                                    v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__1(v___x_1996_, v_declNameNonRec_1935_, v_argsPacker_1937_, v_fixedParamPerms_1936_, v_preDefs_1934_, v___x_1995_, v___x_1998_, v_env_1985_);
                                    leanh::lean_dec_ref(v_preDefs_1934_);
                                    v_nextMacroScope_1947_ = v_nextMacroScope_1986_;
                                    v_ngen_1948_ = v_ngen_1987_;
                                    v_auxDeclNGen_1949_ = v_auxDeclNGen_1988_;
                                    v_traceState_1950_ = v_traceState_1989_;
                                    v_messages_1951_ = v_messages_1990_;
                                    v_infoState_1952_ = v_infoState_1991_;
                                    v_snapshotTasks_1953_ = v_snapshotTasks_1992_;
                                    v___y_1954_ = v___x_1999_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_2000_ = lean_usize_of_nat(v___x_1979_);
                                v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__1(v___x_1996_, v_declNameNonRec_1935_, v_argsPacker_1937_, v_fixedParamPerms_1936_, v_preDefs_1934_, v___x_1995_, v___x_2000_, v_env_1985_);
                                leanh::lean_dec_ref(v_preDefs_1934_);
                                v_nextMacroScope_1947_ = v_nextMacroScope_1986_;
                                v_ngen_1948_ = v_ngen_1987_;
                                v_auxDeclNGen_1949_ = v_auxDeclNGen_1988_;
                                v_traceState_1950_ = v_traceState_1989_;
                                v_messages_1951_ = v_messages_1990_;
                                v_infoState_1952_ = v_infoState_1991_;
                                v_snapshotTasks_1953_ = v_snapshotTasks_1992_;
                                v___y_1954_ = v___x_2001_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_argsPacker_1937_);
                        leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                        leanh::lean_dec(v_declNameNonRec_1935_);
                        leanh::lean_dec_ref(v_preDefs_1934_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_argsPacker_1937_);
                    leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                    leanh::lean_dec(v_declNameNonRec_1935_);
                    leanh::lean_dec_ref(v_preDefs_1934_);
                    v_a_2002_ = leanh::lean_ctor_get(v___y_1981_, 0);
                    v_isSharedCheck_2009_ = (!leanh::lean_is_exclusive(v___y_1981_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2004_ = v___y_1981_;
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2002_);
                        leanh::lean_dec(v___y_1981_);
                        v___x_2004_ = leanh::lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2007_;
            }
            9 => {
                v___x_2011_ = lean_nat_dec_lt(v___x_1978_, v___x_1979_);
                if v___x_2011_ == 0 {
                    leanh::lean_dec_ref(v_argsPacker_1937_);
                    leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                    leanh::lean_dec(v_declNameNonRec_1935_);
                    leanh::lean_dec_ref(v_preDefs_1934_);
                    state = 5;
                    continue;
                } else {
                    if v___x_2011_ == 0 {
                        leanh::lean_dec_ref(v_argsPacker_1937_);
                        leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                        leanh::lean_dec(v_declNameNonRec_1935_);
                        leanh::lean_dec_ref(v_preDefs_1934_);
                        state = 5;
                        continue;
                    } else {
                        v___x_2012_ = 0usize;
                        v___x_2013_ = lean_usize_of_nat(v___x_1979_);
                        v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__2(v_preDefs_1934_, v___x_2012_, v___x_2013_);
                        if v___x_2014_ == 0 {
                            leanh::lean_dec_ref(v_argsPacker_1937_);
                            leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                            leanh::lean_dec(v_declNameNonRec_1935_);
                            leanh::lean_dec_ref(v_preDefs_1934_);
                            state = 5;
                            continue;
                        } else {
                            v___x_2015_ = 0;
                            if v___x_2011_ == 0 {
                                v___x_2016_ = l_Lean_Elab_WF_registerEqnsInfo___lam__0(
                                    v___x_2014_,
                                    v___x_2015_,
                                    v___x_2015_,
                                    v_a_1938_,
                                    v_a_1939_,
                                    v_a_1940_,
                                    v_a_1941_,
                                );
                                v___y_1981_ = v___x_2016_;
                                state = 6;
                                continue;
                            } else {
                                if v___x_2011_ == 0 {
                                    leanh::lean_dec_ref(v_argsPacker_1937_);
                                    leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                                    leanh::lean_dec(v_declNameNonRec_1935_);
                                    leanh::lean_dec_ref(v_preDefs_1934_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_registerEqnsInfo_spec__3(v___x_2014_, v_preDefs_1934_, v___x_2012_, v___x_2013_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
                                    if leanh::lean_obj_tag(v___x_2017_) == 0 {
                                        v_a_2018_ = leanh::lean_ctor_get(v___x_2017_, 0);
                                        leanh::lean_inc(v_a_2018_);
                                        leanh::lean_dec_ref_known(v___x_2017_, 1);
                                        v___x_2019_ = (leanh::lean_unbox(v_a_2018_) as u8);
                                        leanh::lean_dec(v_a_2018_);
                                        v___x_2020_ = l_Lean_Elab_WF_registerEqnsInfo___lam__0(
                                            v___x_2014_,
                                            v___x_2015_,
                                            v___x_2019_,
                                            v_a_1938_,
                                            v_a_1939_,
                                            v_a_1940_,
                                            v_a_1941_,
                                        );
                                        v___y_1981_ = v___x_2020_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___y_1981_ = v___x_2017_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            10 => {
                if leanh::lean_obj_tag(v___y_2022_) == 0 {
                    leanh::lean_dec_ref_known(v___y_2022_, 1);
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_argsPacker_1937_);
                    leanh::lean_dec_ref(v_fixedParamPerms_1936_);
                    leanh::lean_dec(v_declNameNonRec_1935_);
                    leanh::lean_dec_ref(v_preDefs_1934_);
                    return v___y_2022_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_registerEqnsInfo___boxed(
    mut v_preDefs_2032_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2033_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_2034_: *mut leanh::LeanObject,
    mut v_argsPacker_2035_: *mut leanh::LeanObject,
    mut v_a_2036_: *mut leanh::LeanObject,
    mut v_a_2037_: *mut leanh::LeanObject,
    mut v_a_2038_: *mut leanh::LeanObject,
    mut v_a_2039_: *mut leanh::LeanObject,
    mut v_a_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2041_ = l_Lean_Elab_WF_registerEqnsInfo(
        v_preDefs_2032_,
        v_declNameNonRec_2033_,
        v_fixedParamPerms_2034_,
        v_argsPacker_2035_,
        v_a_2036_,
        v_a_2037_,
        v_a_2038_,
        v_a_2039_,
    );
    leanh::lean_dec(v_a_2039_);
    leanh::lean_dec_ref(v_a_2038_);
    leanh::lean_dec(v_a_2037_);
    leanh::lean_dec_ref(v_a_2036_);
    return v_res_2041_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4(
    mut v_as_2042_: *mut leanh::LeanObject,
    mut v_i_2043_: usize,
    mut v_stop_2044_: usize,
    mut v_b_2045_: *mut leanh::LeanObject,
    mut v___y_2046_: *mut leanh::LeanObject,
    mut v___y_2047_: *mut leanh::LeanObject,
    mut v___y_2048_: *mut leanh::LeanObject,
    mut v___y_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4___redArg(v_as_2042_, v_i_2043_, v_stop_2044_, v_b_2045_, v___y_2048_, v___y_2049_);
    return v___x_2051_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4___boxed(
    mut v_as_2052_: *mut leanh::LeanObject,
    mut v_i_2053_: *mut leanh::LeanObject,
    mut v_stop_2054_: *mut leanh::LeanObject,
    mut v_b_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
    mut v___y_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2061_: usize = 0;
    let mut v_stop_boxed_2062_: usize = 0;
    let mut v_res_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2061_ = leanh::lean_unbox_usize(v_i_2053_);
    leanh::lean_dec(v_i_2053_);
    v_stop_boxed_2062_ = leanh::lean_unbox_usize(v_stop_2054_);
    leanh::lean_dec(v_stop_2054_);
    v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_registerEqnsInfo_spec__4(v_as_2052_, v_i_boxed_2061_, v_stop_boxed_2062_, v_b_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
    leanh::lean_dec(v___y_2059_);
    leanh::lean_dec_ref(v___y_2058_);
    leanh::lean_dec(v___y_2057_);
    leanh::lean_dec_ref(v___y_2056_);
    leanh::lean_dec_ref(v_as_2052_);
    return v_res_2063_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = leanh::lean_unsigned_to_nat(32);
    v___x_2065_ = lean_mk_empty_array_with_capacity(v___x_2064_);
    v___x_2066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2066_, 0, v___x_2065_);
    return v___x_2066_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2067_: usize = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = 5usize;
    v___x_2068_ = leanh::lean_unsigned_to_nat(0);
    v___x_2069_ = leanh::lean_unsigned_to_nat(32);
    v___x_2070_ = lean_mk_empty_array_with_capacity(v___x_2069_);
    v___x_2071_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__0);
    v___x_2072_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2072_, 0, v___x_2071_);
    leanh::lean_ctor_set(v___x_2072_, 1, v___x_2070_);
    leanh::lean_ctor_set(v___x_2072_, 2, v___x_2068_);
    leanh::lean_ctor_set(v___x_2072_, 3, v___x_2068_);
    leanh::lean_ctor_set_usize(v___x_2072_, 4, v___x_2067_);
    return v___x_2072_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg(
    mut v___y_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v_tid_2091_: u64 = 0;
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut v_unused_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2075_ = lean_st_ref_get(v___y_2073_);
                v_traceState_2076_ = leanh::lean_ctor_get(v___x_2075_, 4);
                leanh::lean_inc_ref(v_traceState_2076_);
                leanh::lean_dec(v___x_2075_);
                v_traces_2077_ = leanh::lean_ctor_get(v_traceState_2076_, 0);
                leanh::lean_inc_ref(v_traces_2077_);
                leanh::lean_dec_ref(v_traceState_2076_);
                v___x_2078_ = lean_st_ref_take(v___y_2073_);
                v_traceState_2079_ = leanh::lean_ctor_get(v___x_2078_, 4);
                v_env_2080_ = leanh::lean_ctor_get(v___x_2078_, 0);
                v_nextMacroScope_2081_ = leanh::lean_ctor_get(v___x_2078_, 1);
                v_ngen_2082_ = leanh::lean_ctor_get(v___x_2078_, 2);
                v_auxDeclNGen_2083_ = leanh::lean_ctor_get(v___x_2078_, 3);
                v_cache_2084_ = leanh::lean_ctor_get(v___x_2078_, 5);
                v_messages_2085_ = leanh::lean_ctor_get(v___x_2078_, 6);
                v_infoState_2086_ = leanh::lean_ctor_get(v___x_2078_, 7);
                v_snapshotTasks_2087_ = leanh::lean_ctor_get(v___x_2078_, 8);
                v_isSharedCheck_2106_ = (!leanh::lean_is_exclusive(v___x_2078_)) as u8;
                if v_isSharedCheck_2106_ == 0 {
                    v___x_2089_ = v___x_2078_;
                    v_isShared_2090_ = v_isSharedCheck_2106_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2087_);
                    leanh::lean_inc(v_infoState_2086_);
                    leanh::lean_inc(v_messages_2085_);
                    leanh::lean_inc(v_cache_2084_);
                    leanh::lean_inc(v_traceState_2079_);
                    leanh::lean_inc(v_auxDeclNGen_2083_);
                    leanh::lean_inc(v_ngen_2082_);
                    leanh::lean_inc(v_nextMacroScope_2081_);
                    leanh::lean_inc(v_env_2080_);
                    leanh::lean_dec(v___x_2078_);
                    v___x_2089_ = leanh::lean_box(0);
                    v_isShared_2090_ = v_isSharedCheck_2106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_2091_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2079_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2104_ =
                    (!leanh::lean_is_exclusive(v_traceState_2079_)) as u8;
                if v_isSharedCheck_2104_ == 0 {
                    v_unused_2105_ = leanh::lean_ctor_get(v_traceState_2079_, 0);
                    leanh::lean_dec(v_unused_2105_);
                    v___x_2093_ = v_traceState_2079_;
                    v_isShared_2094_ = v_isSharedCheck_2104_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_2079_);
                    v___x_2093_ = leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2095_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___closed__1);
                if v_isShared_2094_ == 0 {
                    leanh::lean_ctor_set(v___x_2093_, 0, v___x_2095_);
                    v___x_2097_ = v___x_2093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2095_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2103_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2091_,
                    );
                    v___x_2097_ = v_reuseFailAlloc_2103_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2090_ == 0 {
                    leanh::lean_ctor_set(v___x_2089_, 4, v___x_2097_);
                    v___x_2099_ = v___x_2089_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2102_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_env_2080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_nextMacroScope_2081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_ngen_2082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_auxDeclNGen_2083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 4, v___x_2097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 5, v_cache_2084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 6, v_messages_2085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 7, v_infoState_2086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 8, v_snapshotTasks_2087_);
                    v___x_2099_ = v_reuseFailAlloc_2102_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2100_ = lean_st_ref_set(v___y_2073_, v___x_2099_);
                v___x_2101_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2101_, 0, v_traces_2077_);
                return v___x_2101_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg___boxed(
    mut v___y_2107_: *mut leanh::LeanObject,
    mut v___y_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg(v___y_2107_);
    leanh::lean_dec(v___y_2107_);
    return v_res_2109_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2(
    mut v___y_2110_: *mut leanh::LeanObject,
    mut v___y_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg(v___y_2113_);
    return v___x_2115_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___boxed(
    mut v___y_2116_: *mut leanh::LeanObject,
    mut v___y_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2121_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2(v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
    leanh::lean_dec(v___y_2119_);
    leanh::lean_dec_ref(v___y_2118_);
    leanh::lean_dec(v___y_2117_);
    leanh::lean_dec_ref(v___y_2116_);
    return v_res_2121_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__3(
    mut v_opts_2122_: *mut leanh::LeanObject,
    mut v_opt_2123_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2124_ = leanh::lean_ctor_get(v_opt_2123_, 0);
    v_defValue_2125_ = leanh::lean_ctor_get(v_opt_2123_, 1);
    v_map_2126_ = leanh::lean_ctor_get(v_opts_2122_, 0);
    v___x_2127_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2126_,
            v_name_2124_,
        );
    if leanh::lean_obj_tag(v___x_2127_) == 0 {
        let mut v___x_2128_: u8 = 0;
        v___x_2128_ = (leanh::lean_unbox(v_defValue_2125_) as u8);
        return v___x_2128_;
    } else {
        let mut v_val_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2129_ = leanh::lean_ctor_get(v___x_2127_, 0);
        leanh::lean_inc(v_val_2129_);
        leanh::lean_dec_ref_known(v___x_2127_, 1);
        if leanh::lean_obj_tag(v_val_2129_) == 1 {
            let mut v_v_2130_: u8 = 0;
            v_v_2130_ = leanh::lean_ctor_get_uint8(v_val_2129_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2129_, 0);
            return v_v_2130_;
        } else {
            let mut v___x_2131_: u8 = 0;
            leanh::lean_dec(v_val_2129_);
            v___x_2131_ = (leanh::lean_unbox(v_defValue_2125_) as u8);
            return v___x_2131_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__3___boxed(
    mut v_opts_2132_: *mut leanh::LeanObject,
    mut v_opt_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2134_: u8 = 0;
    let mut v_r_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2134_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__3(v_opts_2132_, v_opt_2133_);
    leanh::lean_dec_ref(v_opt_2133_);
    leanh::lean_dec_ref(v_opts_2132_);
    v_r_2135_ = leanh::lean_box((v_res_2134_) as usize);
    return v_r_2135_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__0(
    mut v___x_2136_: *mut leanh::LeanObject,
    mut v_hasTrace_2137_: u8,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
    mut v___y_2140_: *mut leanh::LeanObject,
    mut v___y_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_addDecl(v___x_2136_, v_hasTrace_2137_, v___y_2140_, v___y_2141_);
    return v___x_2143_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__0___boxed(
    mut v___x_2144_: *mut leanh::LeanObject,
    mut v_hasTrace_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasTrace_boxed_2151_: u8 = 0;
    let mut v_res_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hasTrace_boxed_2151_ = (leanh::lean_unbox(v_hasTrace_2145_) as u8);
    v_res_2152_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__0(v___x_2144_, v_hasTrace_boxed_2151_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
    leanh::lean_dec(v___y_2149_);
    leanh::lean_dec_ref(v___y_2148_);
    leanh::lean_dec(v___y_2147_);
    leanh::lean_dec_ref(v___y_2146_);
    return v_res_2152_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2154_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__0;
    v___x_2155_ = l_Lean_stringToMessageData(v___x_2154_);
    return v___x_2155_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1(
    mut v_declName_2156_: *mut leanh::LeanObject,
    mut v_x_2157_: *mut leanh::LeanObject,
    mut v___y_2158_: *mut leanh::LeanObject,
    mut v___y_2159_: *mut leanh::LeanObject,
    mut v___y_2160_: *mut leanh::LeanObject,
    mut v___y_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2163_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___closed__1);
    v___x_2164_ = l_Lean_MessageData_ofName(v_declName_2156_);
    v___x_2165_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2165_, 0, v___x_2163_);
    leanh::lean_ctor_set(v___x_2165_, 1, v___x_2164_);
    v___x_2166_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
    return v___x_2166_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___boxed(
    mut v_declName_2167_: *mut leanh::LeanObject,
    mut v_x_2168_: *mut leanh::LeanObject,
    mut v___y_2169_: *mut leanh::LeanObject,
    mut v___y_2170_: *mut leanh::LeanObject,
    mut v___y_2171_: *mut leanh::LeanObject,
    mut v___y_2172_: *mut leanh::LeanObject,
    mut v___y_2173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1(v_declName_2167_, v_x_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
    leanh::lean_dec(v___y_2172_);
    leanh::lean_dec_ref(v___y_2171_);
    leanh::lean_dec(v___y_2170_);
    leanh::lean_dec_ref(v___y_2169_);
    leanh::lean_dec_ref(v_x_2168_);
    return v_res_2174_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__2(
    mut v_____r_2175_: *mut leanh::LeanObject,
    mut v___y_2176_: *mut leanh::LeanObject,
    mut v___y_2177_: *mut leanh::LeanObject,
    mut v___y_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2181_ = leanh::lean_box(0);
    v___x_2182_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2182_, 0, v___x_2181_);
    return v___x_2182_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__2___boxed(
    mut v_____r_2183_: *mut leanh::LeanObject,
    mut v___y_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
    mut v___y_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2189_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__2(v_____r_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
    leanh::lean_dec(v___y_2187_);
    leanh::lean_dec_ref(v___y_2186_);
    leanh::lean_dec(v___y_2185_);
    leanh::lean_dec_ref(v___y_2184_);
    return v_res_2189_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__3(
    mut v___f_2190_: *mut leanh::LeanObject,
    mut v_x_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
    mut v___y_2194_: *mut leanh::LeanObject,
    mut v___y_2195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = leanh::lean_box(0);
    leanh::lean_inc(v___y_2195_);
    leanh::lean_inc_ref(v___y_2194_);
    leanh::lean_inc(v___y_2193_);
    leanh::lean_inc_ref(v___y_2192_);
    v___x_2198_ = leanh::lean_apply_6(
        v___f_2190_,
        v___x_2197_,
        v___y_2192_,
        v___y_2193_,
        v___y_2194_,
        v___y_2195_,
        leanh::lean_box(0),
    );
    return v___x_2198_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__3___boxed(
    mut v___f_2199_: *mut leanh::LeanObject,
    mut v_x_2200_: *mut leanh::LeanObject,
    mut v___y_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
    mut v___y_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
    mut v___y_2205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__3(v___f_2199_, v_x_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
    leanh::lean_dec(v___y_2204_);
    leanh::lean_dec_ref(v___y_2203_);
    leanh::lean_dec(v___y_2202_);
    leanh::lean_dec_ref(v___y_2201_);
    leanh::lean_dec(v_x_2200_);
    return v_res_2206_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__6(
    mut v___x_2207_: *mut leanh::LeanObject,
    mut v___x_2208_: u8,
    mut v___y_2209_: *mut leanh::LeanObject,
    mut v___y_2210_: *mut leanh::LeanObject,
    mut v___y_2211_: *mut leanh::LeanObject,
    mut v___y_2212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = l_Lean_addDecl(v___x_2207_, v___x_2208_, v___y_2211_, v___y_2212_);
    return v___x_2214_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__6___boxed(
    mut v___x_2215_: *mut leanh::LeanObject,
    mut v___x_2216_: *mut leanh::LeanObject,
    mut v___y_2217_: *mut leanh::LeanObject,
    mut v___y_2218_: *mut leanh::LeanObject,
    mut v___y_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_15390__boxed_2222_: u8 = 0;
    let mut v_res_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_15390__boxed_2222_ = (leanh::lean_unbox(v___x_2216_) as u8);
    v_res_2223_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__6(v___x_2215_, v___x_15390__boxed_2222_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
    leanh::lean_dec(v___y_2220_);
    leanh::lean_dec_ref(v___y_2219_);
    leanh::lean_dec(v___y_2218_);
    leanh::lean_dec_ref(v___y_2217_);
    return v_res_2223_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__9(
    mut v_msgData_2224_: *mut leanh::LeanObject,
    mut v___y_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = lean_st_ref_get(v___y_2228_);
    v_env_2231_ = leanh::lean_ctor_get(v___x_2230_, 0);
    leanh::lean_inc_ref(v_env_2231_);
    leanh::lean_dec(v___x_2230_);
    v___x_2232_ = lean_st_ref_get(v___y_2226_);
    v_mctx_2233_ = leanh::lean_ctor_get(v___x_2232_, 0);
    leanh::lean_inc_ref(v_mctx_2233_);
    leanh::lean_dec(v___x_2232_);
    v_lctx_2234_ = leanh::lean_ctor_get(v___y_2225_, 2);
    v_options_2235_ = leanh::lean_ctor_get(v___y_2227_, 2);
    leanh::lean_inc_ref(v_options_2235_);
    leanh::lean_inc_ref(v_lctx_2234_);
    v___x_2236_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2236_, 0, v_env_2231_);
    leanh::lean_ctor_set(v___x_2236_, 1, v_mctx_2233_);
    leanh::lean_ctor_set(v___x_2236_, 2, v_lctx_2234_);
    leanh::lean_ctor_set(v___x_2236_, 3, v_options_2235_);
    v___x_2237_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2237_, 0, v___x_2236_);
    leanh::lean_ctor_set(v___x_2237_, 1, v_msgData_2224_);
    v___x_2238_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2238_, 0, v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__9___boxed(
    mut v_msgData_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
    mut v___y_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: *mut leanh::LeanObject,
    mut v___y_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2245_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__9(v_msgData_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
    leanh::lean_dec(v___y_2243_);
    leanh::lean_dec_ref(v___y_2242_);
    leanh::lean_dec(v___y_2241_);
    leanh::lean_dec_ref(v___y_2240_);
    return v_res_2245_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17___redArg(
    mut v_msg_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2252_ = leanh::lean_ctor_get(v___y_2249_, 5);
                v___x_2253_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__9(v_msg_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
                v_a_2254_ = leanh::lean_ctor_get(v___x_2253_, 0);
                v_isSharedCheck_2262_ = (!leanh::lean_is_exclusive(v___x_2253_)) as u8;
                if v_isSharedCheck_2262_ == 0 {
                    v___x_2256_ = v___x_2253_;
                    v_isShared_2257_ = v_isSharedCheck_2262_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2254_);
                    leanh::lean_dec(v___x_2253_);
                    v___x_2256_ = leanh::lean_box(0);
                    v_isShared_2257_ = v_isSharedCheck_2262_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2252_);
                v___x_2258_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2258_, 0, v_ref_2252_);
                leanh::lean_ctor_set(v___x_2258_, 1, v_a_2254_);
                if v_isShared_2257_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2256_, 1);
                    leanh::lean_ctor_set(v___x_2256_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
                    v___x_2260_ = v_reuseFailAlloc_2261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17___redArg___boxed(
    mut v_msg_2263_: *mut leanh::LeanObject,
    mut v___y_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
    mut v___y_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2269_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17___redArg(v_msg_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
    leanh::lean_dec(v___y_2267_);
    leanh::lean_dec_ref(v___y_2266_);
    leanh::lean_dec(v___y_2265_);
    leanh::lean_dec_ref(v___y_2264_);
    return v_res_2269_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15___redArg(
    mut v_ref_2270_: *mut leanh::LeanObject,
    mut v_msg_2271_: *mut leanh::LeanObject,
    mut v___y_2272_: *mut leanh::LeanObject,
    mut v___y_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
    mut v___y_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2289_: u8 = 0;
    let mut v_cancelTk_x3f_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2291_: u8 = 0;
    let mut v_inheritedTraceOptions_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2277_ = leanh::lean_ctor_get(v___y_2274_, 0);
    v_fileMap_2278_ = leanh::lean_ctor_get(v___y_2274_, 1);
    v_options_2279_ = leanh::lean_ctor_get(v___y_2274_, 2);
    v_currRecDepth_2280_ = leanh::lean_ctor_get(v___y_2274_, 3);
    v_maxRecDepth_2281_ = leanh::lean_ctor_get(v___y_2274_, 4);
    v_ref_2282_ = leanh::lean_ctor_get(v___y_2274_, 5);
    v_currNamespace_2283_ = leanh::lean_ctor_get(v___y_2274_, 6);
    v_openDecls_2284_ = leanh::lean_ctor_get(v___y_2274_, 7);
    v_initHeartbeats_2285_ = leanh::lean_ctor_get(v___y_2274_, 8);
    v_maxHeartbeats_2286_ = leanh::lean_ctor_get(v___y_2274_, 9);
    v_quotContext_2287_ = leanh::lean_ctor_get(v___y_2274_, 10);
    v_currMacroScope_2288_ = leanh::lean_ctor_get(v___y_2274_, 11);
    v_diag_2289_ = leanh::lean_ctor_get_uint8(
        v___y_2274_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2290_ = leanh::lean_ctor_get(v___y_2274_, 12);
    v_suppressElabErrors_2291_ = leanh::lean_ctor_get_uint8(
        v___y_2274_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2292_ = leanh::lean_ctor_get(v___y_2274_, 13);
    v_ref_2293_ = l_Lean_replaceRef(v_ref_2270_, v_ref_2282_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2292_);
    leanh::lean_inc(v_cancelTk_x3f_2290_);
    leanh::lean_inc(v_currMacroScope_2288_);
    leanh::lean_inc(v_quotContext_2287_);
    leanh::lean_inc(v_maxHeartbeats_2286_);
    leanh::lean_inc(v_initHeartbeats_2285_);
    leanh::lean_inc(v_openDecls_2284_);
    leanh::lean_inc(v_currNamespace_2283_);
    leanh::lean_inc(v_maxRecDepth_2281_);
    leanh::lean_inc(v_currRecDepth_2280_);
    leanh::lean_inc_ref(v_options_2279_);
    leanh::lean_inc_ref(v_fileMap_2278_);
    leanh::lean_inc_ref(v_fileName_2277_);
    v___x_2294_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2294_, 0, v_fileName_2277_);
    leanh::lean_ctor_set(v___x_2294_, 1, v_fileMap_2278_);
    leanh::lean_ctor_set(v___x_2294_, 2, v_options_2279_);
    leanh::lean_ctor_set(v___x_2294_, 3, v_currRecDepth_2280_);
    leanh::lean_ctor_set(v___x_2294_, 4, v_maxRecDepth_2281_);
    leanh::lean_ctor_set(v___x_2294_, 5, v_ref_2293_);
    leanh::lean_ctor_set(v___x_2294_, 6, v_currNamespace_2283_);
    leanh::lean_ctor_set(v___x_2294_, 7, v_openDecls_2284_);
    leanh::lean_ctor_set(v___x_2294_, 8, v_initHeartbeats_2285_);
    leanh::lean_ctor_set(v___x_2294_, 9, v_maxHeartbeats_2286_);
    leanh::lean_ctor_set(v___x_2294_, 10, v_quotContext_2287_);
    leanh::lean_ctor_set(v___x_2294_, 11, v_currMacroScope_2288_);
    leanh::lean_ctor_set(v___x_2294_, 12, v_cancelTk_x3f_2290_);
    leanh::lean_ctor_set(v___x_2294_, 13, v_inheritedTraceOptions_2292_);
    leanh::lean_ctor_set_uint8(
        v___x_2294_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2289_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2294_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2291_,
    );
    v___x_2295_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17___redArg(v_msg_2271_, v___y_2272_, v___y_2273_, v___x_2294_, v___y_2275_);
    leanh::lean_dec_ref_known(v___x_2294_, 14);
    return v___x_2295_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15___redArg___boxed(
    mut v_ref_2296_: *mut leanh::LeanObject,
    mut v_msg_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2303_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15___redArg(v_ref_2296_, v_msg_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
    leanh::lean_dec(v___y_2301_);
    leanh::lean_dec_ref(v___y_2300_);
    leanh::lean_dec(v___y_2299_);
    leanh::lean_dec_ref(v___y_2298_);
    leanh::lean_dec(v_ref_2296_);
    return v_res_2303_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2304_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__0);
    v___x_2306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2306_, 0, v___x_2305_);
    return v___x_2306_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1);
    v___x_2308_ = leanh::lean_unsigned_to_nat(0);
    v___x_2309_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2309_, 0, v___x_2308_);
    leanh::lean_ctor_set(v___x_2309_, 1, v___x_2308_);
    leanh::lean_ctor_set(v___x_2309_, 2, v___x_2308_);
    leanh::lean_ctor_set(v___x_2309_, 3, v___x_2308_);
    leanh::lean_ctor_set(v___x_2309_, 4, v___x_2307_);
    leanh::lean_ctor_set(v___x_2309_, 5, v___x_2307_);
    leanh::lean_ctor_set(v___x_2309_, 6, v___x_2307_);
    leanh::lean_ctor_set(v___x_2309_, 7, v___x_2307_);
    leanh::lean_ctor_set(v___x_2309_, 8, v___x_2307_);
    leanh::lean_ctor_set(v___x_2309_, 9, v___x_2307_);
    return v___x_2309_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = leanh::lean_unsigned_to_nat(32);
    v___x_2311_ = lean_mk_empty_array_with_capacity(v___x_2310_);
    v___x_2312_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    return v___x_2312_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2313_: usize = 0;
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = 5usize;
    v___x_2314_ = leanh::lean_unsigned_to_nat(0);
    v___x_2315_ = leanh::lean_unsigned_to_nat(32);
    v___x_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
    v___x_2317_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__3);
    v___x_2318_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2318_, 0, v___x_2317_);
    leanh::lean_ctor_set(v___x_2318_, 1, v___x_2316_);
    leanh::lean_ctor_set(v___x_2318_, 2, v___x_2314_);
    leanh::lean_ctor_set(v___x_2318_, 3, v___x_2314_);
    leanh::lean_ctor_set_usize(v___x_2318_, 4, v___x_2313_);
    return v___x_2318_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ = leanh::lean_box(1);
    v___x_2320_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__4);
    v___x_2321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__1);
    v___x_2322_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2322_, 0, v___x_2321_);
    leanh::lean_ctor_set(v___x_2322_, 1, v___x_2320_);
    leanh::lean_ctor_set(v___x_2322_, 2, v___x_2319_);
    return v___x_2322_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2324_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__6;
    v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
    return v___x_2325_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__8;
    v___x_2328_ = l_Lean_stringToMessageData(v___x_2327_);
    return v___x_2328_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__10;
    v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
    return v___x_2331_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__12;
    v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
    return v___x_2334_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__14;
    v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2339_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__16;
    v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
    return v___x_2340_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__18;
    v___x_2343_ = l_Lean_stringToMessageData(v___x_2342_);
    return v___x_2343_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg(
    mut v_msg_2344_: *mut leanh::LeanObject,
    mut v_declHint_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: u8 = 0;
    let mut v_isExporting_2351_: u8 = 0;
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2405_: u8 = 0;
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2348_ = lean_st_ref_get(v___y_2346_);
                v_env_2349_ = leanh::lean_ctor_get(v___x_2348_, 0);
                leanh::lean_inc_ref(v_env_2349_);
                leanh::lean_dec(v___x_2348_);
                v___x_2350_ = l_Lean_Name_isAnonymous(v_declHint_2345_);
                if v___x_2350_ == 0 {
                    v_isExporting_2351_ = leanh::lean_ctor_get_uint8(
                        v_env_2349_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2351_ == 0 {
                        leanh::lean_dec_ref(v_env_2349_);
                        leanh::lean_dec(v_declHint_2345_);
                        v___x_2352_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2352_, 0, v_msg_2344_);
                        return v___x_2352_;
                    } else {
                        leanh::lean_inc_ref(v_env_2349_);
                        v___x_2353_ = l_Lean_Environment_setExporting(v_env_2349_, v___x_2350_);
                        leanh::lean_inc(v_declHint_2345_);
                        leanh::lean_inc_ref(v___x_2353_);
                        v___x_2354_ = l_Lean_Environment_contains(
                            v___x_2353_,
                            v_declHint_2345_,
                            v_isExporting_2351_,
                        );
                        if v___x_2354_ == 0 {
                            leanh::lean_dec_ref(v___x_2353_);
                            leanh::lean_dec_ref(v_env_2349_);
                            leanh::lean_dec(v_declHint_2345_);
                            v___x_2355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2355_, 0, v_msg_2344_);
                            return v___x_2355_;
                        } else {
                            v___x_2356_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__2);
                            v___x_2357_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__5);
                            v___x_2358_ = l_Lean_Options_empty;
                            v___x_2359_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2359_, 0, v___x_2353_);
                            leanh::lean_ctor_set(v___x_2359_, 1, v___x_2356_);
                            leanh::lean_ctor_set(v___x_2359_, 2, v___x_2357_);
                            leanh::lean_ctor_set(v___x_2359_, 3, v___x_2358_);
                            leanh::lean_inc(v_declHint_2345_);
                            v___x_2360_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2345_, v___x_2350_);
                            v_c_2361_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_2361_, 0, v___x_2359_);
                            leanh::lean_ctor_set(v_c_2361_, 1, v___x_2360_);
                            v___x_2362_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2349_,
                                v_declHint_2345_,
                            );
                            if leanh::lean_obj_tag(v___x_2362_) == 0 {
                                leanh::lean_dec_ref(v_env_2349_);
                                leanh::lean_dec(v_declHint_2345_);
                                v___x_2363_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7);
                                v___x_2364_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2364_, 0, v___x_2363_);
                                leanh::lean_ctor_set(v___x_2364_, 1, v_c_2361_);
                                v___x_2365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__9);
                                v___x_2366_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2366_, 0, v___x_2364_);
                                leanh::lean_ctor_set(v___x_2366_, 1, v___x_2365_);
                                v___x_2367_ = l_Lean_MessageData_note(v___x_2366_);
                                v___x_2368_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2368_, 0, v_msg_2344_);
                                leanh::lean_ctor_set(v___x_2368_, 1, v___x_2367_);
                                v___x_2369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
                                return v___x_2369_;
                            } else {
                                v_val_2370_ = leanh::lean_ctor_get(v___x_2362_, 0);
                                v_isSharedCheck_2405_ =
                                    (!leanh::lean_is_exclusive(v___x_2362_)) as u8;
                                if v_isSharedCheck_2405_ == 0 {
                                    v___x_2372_ = v___x_2362_;
                                    v_isShared_2373_ = v_isSharedCheck_2405_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_2370_);
                                    leanh::lean_dec(v___x_2362_);
                                    v___x_2372_ = leanh::lean_box(0);
                                    v_isShared_2373_ = v_isSharedCheck_2405_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2349_);
                    leanh::lean_dec(v_declHint_2345_);
                    v___x_2406_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2406_, 0, v_msg_2344_);
                    return v___x_2406_;
                }
            }
            1 => {
                v___x_2374_ = leanh::lean_box(0);
                v___x_2375_ = l_Lean_Environment_header(v_env_2349_);
                leanh::lean_dec_ref(v_env_2349_);
                v___x_2376_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2375_);
                v_mod_2377_ = lean_array_get(v___x_2374_, v___x_2376_, v_val_2370_);
                leanh::lean_dec(v_val_2370_);
                leanh::lean_dec_ref(v___x_2376_);
                v___x_2378_ = l_Lean_isPrivateName(v_declHint_2345_);
                leanh::lean_dec(v_declHint_2345_);
                if v___x_2378_ == 0 {
                    v___x_2379_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__11);
                    v___x_2380_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2380_, 0, v___x_2379_);
                    leanh::lean_ctor_set(v___x_2380_, 1, v_c_2361_);
                    v___x_2381_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__13);
                    v___x_2382_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2382_, 0, v___x_2380_);
                    leanh::lean_ctor_set(v___x_2382_, 1, v___x_2381_);
                    v___x_2383_ = l_Lean_MessageData_ofName(v_mod_2377_);
                    v___x_2384_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2384_, 0, v___x_2382_);
                    leanh::lean_ctor_set(v___x_2384_, 1, v___x_2383_);
                    v___x_2385_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__15);
                    v___x_2386_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2386_, 0, v___x_2384_);
                    leanh::lean_ctor_set(v___x_2386_, 1, v___x_2385_);
                    v___x_2387_ = l_Lean_MessageData_note(v___x_2386_);
                    v___x_2388_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2388_, 0, v_msg_2344_);
                    leanh::lean_ctor_set(v___x_2388_, 1, v___x_2387_);
                    if v_isShared_2373_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2372_, 0);
                        leanh::lean_ctor_set(v___x_2372_, 0, v___x_2388_);
                        v___x_2390_ = v___x_2372_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2391_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
                        v___x_2390_ = v_reuseFailAlloc_2391_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2392_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__7);
                    v___x_2393_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                    leanh::lean_ctor_set(v___x_2393_, 1, v_c_2361_);
                    v___x_2394_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__17);
                    v___x_2395_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2395_, 0, v___x_2393_);
                    leanh::lean_ctor_set(v___x_2395_, 1, v___x_2394_);
                    v___x_2396_ = l_Lean_MessageData_ofName(v_mod_2377_);
                    v___x_2397_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2397_, 0, v___x_2395_);
                    leanh::lean_ctor_set(v___x_2397_, 1, v___x_2396_);
                    v___x_2398_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___closed__19);
                    v___x_2399_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2399_, 0, v___x_2397_);
                    leanh::lean_ctor_set(v___x_2399_, 1, v___x_2398_);
                    v___x_2400_ = l_Lean_MessageData_note(v___x_2399_);
                    v___x_2401_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2401_, 0, v_msg_2344_);
                    leanh::lean_ctor_set(v___x_2401_, 1, v___x_2400_);
                    if v_isShared_2373_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2372_, 0);
                        leanh::lean_ctor_set(v___x_2372_, 0, v___x_2401_);
                        v___x_2403_ = v___x_2372_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
                        v___x_2403_ = v_reuseFailAlloc_2404_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2390_;
            }
            3 => {
                return v___x_2403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg___boxed(
    mut v_msg_2407_: *mut leanh::LeanObject,
    mut v_declHint_2408_: *mut leanh::LeanObject,
    mut v___y_2409_: *mut leanh::LeanObject,
    mut v___y_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg(v_msg_2407_, v_declHint_2408_, v___y_2409_);
    leanh::lean_dec(v___y_2409_);
    return v_res_2411_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14(
    mut v_msg_2412_: *mut leanh::LeanObject,
    mut v_declHint_2413_: *mut leanh::LeanObject,
    mut v___y_2414_: *mut leanh::LeanObject,
    mut v___y_2415_: *mut leanh::LeanObject,
    mut v___y_2416_: *mut leanh::LeanObject,
    mut v___y_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2419_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg(v_msg_2412_, v_declHint_2413_, v___y_2417_);
                v_a_2420_ = leanh::lean_ctor_get(v___x_2419_, 0);
                v_isSharedCheck_2429_ = (!leanh::lean_is_exclusive(v___x_2419_)) as u8;
                if v_isSharedCheck_2429_ == 0 {
                    v___x_2422_ = v___x_2419_;
                    v_isShared_2423_ = v_isSharedCheck_2429_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2420_);
                    leanh::lean_dec(v___x_2419_);
                    v___x_2422_ = leanh::lean_box(0);
                    v_isShared_2423_ = v_isSharedCheck_2429_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2424_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2425_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                leanh::lean_ctor_set(v___x_2425_, 1, v_a_2420_);
                if v_isShared_2423_ == 0 {
                    leanh::lean_ctor_set(v___x_2422_, 0, v___x_2425_);
                    v___x_2427_ = v___x_2422_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
                    v___x_2427_ = v_reuseFailAlloc_2428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14___boxed(
    mut v_msg_2430_: *mut leanh::LeanObject,
    mut v_declHint_2431_: *mut leanh::LeanObject,
    mut v___y_2432_: *mut leanh::LeanObject,
    mut v___y_2433_: *mut leanh::LeanObject,
    mut v___y_2434_: *mut leanh::LeanObject,
    mut v___y_2435_: *mut leanh::LeanObject,
    mut v___y_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14(v_msg_2430_, v_declHint_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
    leanh::lean_dec(v___y_2435_);
    leanh::lean_dec_ref(v___y_2434_);
    leanh::lean_dec(v___y_2433_);
    leanh::lean_dec_ref(v___y_2432_);
    return v_res_2437_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12___redArg(
    mut v_ref_2438_: *mut leanh::LeanObject,
    mut v_msg_2439_: *mut leanh::LeanObject,
    mut v_declHint_2440_: *mut leanh::LeanObject,
    mut v___y_2441_: *mut leanh::LeanObject,
    mut v___y_2442_: *mut leanh::LeanObject,
    mut v___y_2443_: *mut leanh::LeanObject,
    mut v___y_2444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14(v_msg_2439_, v_declHint_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
    v_a_2447_ = leanh::lean_ctor_get(v___x_2446_, 0);
    leanh::lean_inc(v_a_2447_);
    leanh::lean_dec_ref(v___x_2446_);
    v___x_2448_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15___redArg(v_ref_2438_, v_a_2447_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
    return v___x_2448_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12___redArg___boxed(
    mut v_ref_2449_: *mut leanh::LeanObject,
    mut v_msg_2450_: *mut leanh::LeanObject,
    mut v_declHint_2451_: *mut leanh::LeanObject,
    mut v___y_2452_: *mut leanh::LeanObject,
    mut v___y_2453_: *mut leanh::LeanObject,
    mut v___y_2454_: *mut leanh::LeanObject,
    mut v___y_2455_: *mut leanh::LeanObject,
    mut v___y_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2457_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12___redArg(v_ref_2449_, v_msg_2450_, v_declHint_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
    leanh::lean_dec(v___y_2455_);
    leanh::lean_dec_ref(v___y_2454_);
    leanh::lean_dec(v___y_2453_);
    leanh::lean_dec_ref(v___y_2452_);
    leanh::lean_dec(v_ref_2449_);
    return v_res_2457_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__0;
    v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__2;
    v___x_2463_ = l_Lean_stringToMessageData(v___x_2462_);
    return v___x_2463_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg(
    mut v_ref_2464_: *mut leanh::LeanObject,
    mut v_constName_2465_: *mut leanh::LeanObject,
    mut v___y_2466_: *mut leanh::LeanObject,
    mut v___y_2467_: *mut leanh::LeanObject,
    mut v___y_2468_: *mut leanh::LeanObject,
    mut v___y_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__1);
    v___x_2472_ = 0;
    leanh::lean_inc(v_constName_2465_);
    v___x_2473_ = l_Lean_MessageData_ofConstName(v_constName_2465_, v___x_2472_);
    v___x_2474_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2471_);
    leanh::lean_ctor_set(v___x_2474_, 1, v___x_2473_);
    v___x_2475_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___closed__3);
    v___x_2476_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2476_, 0, v___x_2474_);
    leanh::lean_ctor_set(v___x_2476_, 1, v___x_2475_);
    v___x_2477_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12___redArg(v_ref_2464_, v___x_2476_, v_constName_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
    return v___x_2477_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg___boxed(
    mut v_ref_2478_: *mut leanh::LeanObject,
    mut v_constName_2479_: *mut leanh::LeanObject,
    mut v___y_2480_: *mut leanh::LeanObject,
    mut v___y_2481_: *mut leanh::LeanObject,
    mut v___y_2482_: *mut leanh::LeanObject,
    mut v___y_2483_: *mut leanh::LeanObject,
    mut v___y_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2485_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_ref_2478_, v_constName_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
    leanh::lean_dec(v___y_2483_);
    leanh::lean_dec_ref(v___y_2482_);
    leanh::lean_dec(v___y_2481_);
    leanh::lean_dec_ref(v___y_2480_);
    leanh::lean_dec(v_ref_2478_);
    return v_res_2485_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3___redArg(
    mut v_constName_2486_: *mut leanh::LeanObject,
    mut v___y_2487_: *mut leanh::LeanObject,
    mut v___y_2488_: *mut leanh::LeanObject,
    mut v___y_2489_: *mut leanh::LeanObject,
    mut v___y_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2492_ = leanh::lean_ctor_get(v___y_2489_, 5);
    v___x_2493_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_ref_2492_, v_constName_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
    return v___x_2493_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_constName_2494_: *mut leanh::LeanObject,
    mut v___y_2495_: *mut leanh::LeanObject,
    mut v___y_2496_: *mut leanh::LeanObject,
    mut v___y_2497_: *mut leanh::LeanObject,
    mut v___y_2498_: *mut leanh::LeanObject,
    mut v___y_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2500_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3___redArg(v_constName_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
    leanh::lean_dec(v___y_2498_);
    leanh::lean_dec_ref(v___y_2497_);
    leanh::lean_dec(v___y_2496_);
    leanh::lean_dec_ref(v___y_2495_);
    return v_res_2500_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0(
    mut v_constName_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
    mut v___y_2504_: *mut leanh::LeanObject,
    mut v___y_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2507_ = lean_st_ref_get(v___y_2505_);
                v_env_2508_ = leanh::lean_ctor_get(v___x_2507_, 0);
                leanh::lean_inc_ref(v_env_2508_);
                leanh::lean_dec(v___x_2507_);
                v___x_2509_ = 0;
                leanh::lean_inc(v_constName_2501_);
                v___x_2510_ =
                    l_Lean_Environment_find_x3f(v_env_2508_, v_constName_2501_, v___x_2509_);
                if leanh::lean_obj_tag(v___x_2510_) == 0 {
                    v___x_2511_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3___redArg(v_constName_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
                    return v___x_2511_;
                } else {
                    leanh::lean_dec(v_constName_2501_);
                    v_val_2512_ = leanh::lean_ctor_get(v___x_2510_, 0);
                    v_isSharedCheck_2519_ = (!leanh::lean_is_exclusive(v___x_2510_)) as u8;
                    if v_isSharedCheck_2519_ == 0 {
                        v___x_2514_ = v___x_2510_;
                        v_isShared_2515_ = v_isSharedCheck_2519_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2512_);
                        leanh::lean_dec(v___x_2510_);
                        v___x_2514_ = leanh::lean_box(0);
                        v_isShared_2515_ = v_isSharedCheck_2519_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2515_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2514_, 0);
                    v___x_2517_ = v___x_2514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_val_2512_);
                    v___x_2517_ = v_reuseFailAlloc_2518_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0___boxed(
    mut v_constName_2520_: *mut leanh::LeanObject,
    mut v___y_2521_: *mut leanh::LeanObject,
    mut v___y_2522_: *mut leanh::LeanObject,
    mut v___y_2523_: *mut leanh::LeanObject,
    mut v___y_2524_: *mut leanh::LeanObject,
    mut v___y_2525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2526_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0(v_constName_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
    leanh::lean_dec(v___y_2524_);
    leanh::lean_dec_ref(v___y_2523_);
    leanh::lean_dec(v___y_2522_);
    leanh::lean_dec_ref(v___y_2521_);
    return v_res_2526_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0(
    mut v_declName_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_isSharedCheck_2560_: u8 = 0;
    let mut v_unused_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_2527_);
                v___x_2533_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0(v_declName_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
                if leanh::lean_obj_tag(v___x_2533_) == 0 {
                    v_isSharedCheck_2560_ = (!leanh::lean_is_exclusive(v___x_2533_)) as u8;
                    if v_isSharedCheck_2560_ == 0 {
                        v_unused_2561_ = leanh::lean_ctor_get(v___x_2533_, 0);
                        leanh::lean_dec(v_unused_2561_);
                        v___x_2535_ = v___x_2533_;
                        v_isShared_2536_ = v_isSharedCheck_2560_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2533_);
                        v___x_2535_ = leanh::lean_box(0);
                        v_isShared_2536_ = v_isSharedCheck_2560_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_2527_);
                    v_a_2562_ = leanh::lean_ctor_get(v___x_2533_, 0);
                    v_isSharedCheck_2569_ = (!leanh::lean_is_exclusive(v___x_2533_)) as u8;
                    if v_isSharedCheck_2569_ == 0 {
                        v___x_2564_ = v___x_2533_;
                        v_isShared_2565_ = v_isSharedCheck_2569_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2562_);
                        leanh::lean_dec(v___x_2533_);
                        v___x_2564_ = leanh::lean_box(0);
                        v_isShared_2565_ = v_isSharedCheck_2569_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2537_ = lean_st_ref_get(v___y_2531_);
                v_env_2538_ = leanh::lean_ctor_get(v___x_2537_, 0);
                leanh::lean_inc_ref(v_env_2538_);
                leanh::lean_dec(v___x_2537_);
                v___x_2539_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2538_, v_declName_2527_);
                leanh::lean_dec(v_declName_2527_);
                leanh::lean_dec_ref(v_env_2538_);
                if leanh::lean_obj_tag(v___x_2539_) == 0 {
                    v___x_2540_ = leanh::lean_box(0);
                    if v_isShared_2536_ == 0 {
                        leanh::lean_ctor_set(v___x_2535_, 0, v___x_2540_);
                        v___x_2542_ = v___x_2535_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
                        v___x_2542_ = v_reuseFailAlloc_2543_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_2544_ = leanh::lean_ctor_get(v___x_2539_, 0);
                    v_isSharedCheck_2559_ = (!leanh::lean_is_exclusive(v___x_2539_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2546_ = v___x_2539_;
                        v_isShared_2547_ = v_isSharedCheck_2559_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2544_);
                        leanh::lean_dec(v___x_2539_);
                        v___x_2546_ = leanh::lean_box(0);
                        v_isShared_2547_ = v_isSharedCheck_2559_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2542_;
            }
            3 => {
                v___x_2548_ = lean_st_ref_get(v___y_2531_);
                v_env_2549_ = leanh::lean_ctor_get(v___x_2548_, 0);
                leanh::lean_inc_ref(v_env_2549_);
                leanh::lean_dec(v___x_2548_);
                v___x_2550_ = leanh::lean_box(0);
                v___x_2551_ = l_Lean_Environment_allImportedModuleNames(v_env_2549_);
                leanh::lean_dec_ref(v_env_2549_);
                v___x_2552_ = lean_array_get(v___x_2550_, v___x_2551_, v_val_2544_);
                leanh::lean_dec(v_val_2544_);
                leanh::lean_dec_ref(v___x_2551_);
                if v_isShared_2547_ == 0 {
                    leanh::lean_ctor_set(v___x_2546_, 0, v___x_2552_);
                    v___x_2554_ = v___x_2546_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2552_);
                    v___x_2554_ = v_reuseFailAlloc_2558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2536_ == 0 {
                    leanh::lean_ctor_set(v___x_2535_, 0, v___x_2554_);
                    v___x_2556_ = v___x_2535_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2557_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
                    v___x_2556_ = v_reuseFailAlloc_2557_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2556_;
            }
            6 => {
                if v_isShared_2565_ == 0 {
                    v___x_2567_ = v___x_2564_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
                    v___x_2567_ = v_reuseFailAlloc_2568_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0___boxed(
    mut v_declName_2570_: *mut leanh::LeanObject,
    mut v___y_2571_: *mut leanh::LeanObject,
    mut v___y_2572_: *mut leanh::LeanObject,
    mut v___y_2573_: *mut leanh::LeanObject,
    mut v___y_2574_: *mut leanh::LeanObject,
    mut v___y_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0(v_declName_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
    leanh::lean_dec(v___y_2574_);
    leanh::lean_dec_ref(v___y_2573_);
    leanh::lean_dec(v___y_2572_);
    leanh::lean_dec_ref(v___y_2571_);
    return v_res_2576_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7___redArg(
    mut v_x_2577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2582_: u8 = 0;
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_a_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2590_: u8 = 0;
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2577_) == 0 {
                    v_a_2579_ = leanh::lean_ctor_get(v_x_2577_, 0);
                    v_isSharedCheck_2586_ = (!leanh::lean_is_exclusive(v_x_2577_)) as u8;
                    if v_isSharedCheck_2586_ == 0 {
                        v___x_2581_ = v_x_2577_;
                        v_isShared_2582_ = v_isSharedCheck_2586_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2579_);
                        leanh::lean_dec(v_x_2577_);
                        v___x_2581_ = leanh::lean_box(0);
                        v_isShared_2582_ = v_isSharedCheck_2586_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2587_ = leanh::lean_ctor_get(v_x_2577_, 0);
                    v_isSharedCheck_2594_ = (!leanh::lean_is_exclusive(v_x_2577_)) as u8;
                    if v_isSharedCheck_2594_ == 0 {
                        v___x_2589_ = v_x_2577_;
                        v_isShared_2590_ = v_isSharedCheck_2594_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2587_);
                        leanh::lean_dec(v_x_2577_);
                        v___x_2589_ = leanh::lean_box(0);
                        v_isShared_2590_ = v_isSharedCheck_2594_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2582_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2581_, 1);
                    v___x_2584_ = v___x_2581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2584_;
            }
            3 => {
                if v_isShared_2590_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2589_, 0);
                    v___x_2592_ = v___x_2589_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
                    v___x_2592_ = v_reuseFailAlloc_2593_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7___redArg___boxed(
    mut v_x_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2597_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7___redArg(v_x_2595_);
    return v_res_2597_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__5(
    mut v_e_2598_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_2598_) == 0 {
        let mut v___x_2599_: u8 = 0;
        v___x_2599_ = 2;
        return v___x_2599_;
    } else {
        let mut v_a_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2600_ = leanh::lean_ctor_get(v_e_2598_, 0);
        if leanh::lean_obj_tag(v_a_2600_) == 0 {
            let mut v___x_2601_: u8 = 0;
            v___x_2601_ = 1;
            return v___x_2601_;
        } else {
            let mut v___x_2602_: u8 = 0;
            v___x_2602_ = 0;
            return v___x_2602_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__5___boxed(
    mut v_e_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2604_: u8 = 0;
    let mut v_r_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__5(v_e_2603_);
    leanh::lean_dec_ref(v_e_2603_);
    v_r_2605_ = leanh::lean_box((v_res_2604_) as usize);
    return v_r_2605_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__8(
    mut v_sz_2606_: usize,
    mut v_i_2607_: usize,
    mut v_bs_2608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2609_: u8 = 0;
    let mut v_v_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: usize = 0;
    let mut v___x_2615_: usize = 0;
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2609_ = lean_usize_dec_lt(v_i_2607_, v_sz_2606_);
                if v___x_2609_ == 0 {
                    return v_bs_2608_;
                } else {
                    v_v_2610_ = lean_array_uget_borrowed(v_bs_2608_, v_i_2607_);
                    v_msg_2611_ = leanh::lean_ctor_get(v_v_2610_, 1);
                    leanh::lean_inc_ref(v_msg_2611_);
                    v___x_2612_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2613_ = lean_array_uset(v_bs_2608_, v_i_2607_, v___x_2612_);
                    v___x_2614_ = 1usize;
                    v___x_2615_ = lean_usize_add(v_i_2607_, v___x_2614_);
                    v___x_2616_ = lean_array_uset(v_bs_x27_2613_, v_i_2607_, v_msg_2611_);
                    v_i_2607_ = v___x_2615_;
                    v_bs_2608_ = v___x_2616_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__8___boxed(
    mut v_sz_2618_: *mut leanh::LeanObject,
    mut v_i_2619_: *mut leanh::LeanObject,
    mut v_bs_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2621_: usize = 0;
    let mut v_i_boxed_2622_: usize = 0;
    let mut v_res_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2621_ = leanh::lean_unbox_usize(v_sz_2618_);
    leanh::lean_dec(v_sz_2618_);
    v_i_boxed_2622_ = leanh::lean_unbox_usize(v_i_2619_);
    leanh::lean_dec(v_i_2619_);
    v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__8(v_sz_boxed_2621_, v_i_boxed_2622_, v_bs_2620_);
    return v_res_2623_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6(
    mut v_oldTraces_2624_: *mut leanh::LeanObject,
    mut v_data_2625_: *mut leanh::LeanObject,
    mut v_ref_2626_: *mut leanh::LeanObject,
    mut v_msg_2627_: *mut leanh::LeanObject,
    mut v___y_2628_: *mut leanh::LeanObject,
    mut v___y_2629_: *mut leanh::LeanObject,
    mut v___y_2630_: *mut leanh::LeanObject,
    mut v___y_2631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2645_: u8 = 0;
    let mut v_cancelTk_x3f_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2647_: u8 = 0;
    let mut v_inheritedTraceOptions_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2655_: usize = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2663_: u8 = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v_tid_2677_: u64 = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2680_: u8 = 0;
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut v_unused_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2633_ = leanh::lean_ctor_get(v___y_2630_, 0);
                v_fileMap_2634_ = leanh::lean_ctor_get(v___y_2630_, 1);
                v_options_2635_ = leanh::lean_ctor_get(v___y_2630_, 2);
                v_currRecDepth_2636_ = leanh::lean_ctor_get(v___y_2630_, 3);
                v_maxRecDepth_2637_ = leanh::lean_ctor_get(v___y_2630_, 4);
                v_ref_2638_ = leanh::lean_ctor_get(v___y_2630_, 5);
                v_currNamespace_2639_ = leanh::lean_ctor_get(v___y_2630_, 6);
                v_openDecls_2640_ = leanh::lean_ctor_get(v___y_2630_, 7);
                v_initHeartbeats_2641_ = leanh::lean_ctor_get(v___y_2630_, 8);
                v_maxHeartbeats_2642_ = leanh::lean_ctor_get(v___y_2630_, 9);
                v_quotContext_2643_ = leanh::lean_ctor_get(v___y_2630_, 10);
                v_currMacroScope_2644_ = leanh::lean_ctor_get(v___y_2630_, 11);
                v_diag_2645_ = leanh::lean_ctor_get_uint8(
                    v___y_2630_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2646_ = leanh::lean_ctor_get(v___y_2630_, 12);
                v_suppressElabErrors_2647_ = leanh::lean_ctor_get_uint8(
                    v___y_2630_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2648_ = leanh::lean_ctor_get(v___y_2630_, 13);
                v___x_2649_ = lean_st_ref_get(v___y_2631_);
                v_traceState_2650_ = leanh::lean_ctor_get(v___x_2649_, 4);
                leanh::lean_inc_ref(v_traceState_2650_);
                leanh::lean_dec(v___x_2649_);
                v_traces_2651_ = leanh::lean_ctor_get(v_traceState_2650_, 0);
                leanh::lean_inc_ref(v_traces_2651_);
                leanh::lean_dec_ref(v_traceState_2650_);
                v_ref_2652_ = l_Lean_replaceRef(v_ref_2626_, v_ref_2638_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2648_);
                leanh::lean_inc(v_cancelTk_x3f_2646_);
                leanh::lean_inc(v_currMacroScope_2644_);
                leanh::lean_inc(v_quotContext_2643_);
                leanh::lean_inc(v_maxHeartbeats_2642_);
                leanh::lean_inc(v_initHeartbeats_2641_);
                leanh::lean_inc(v_openDecls_2640_);
                leanh::lean_inc(v_currNamespace_2639_);
                leanh::lean_inc(v_maxRecDepth_2637_);
                leanh::lean_inc(v_currRecDepth_2636_);
                leanh::lean_inc_ref(v_options_2635_);
                leanh::lean_inc_ref(v_fileMap_2634_);
                leanh::lean_inc_ref(v_fileName_2633_);
                v___x_2653_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2653_, 0, v_fileName_2633_);
                leanh::lean_ctor_set(v___x_2653_, 1, v_fileMap_2634_);
                leanh::lean_ctor_set(v___x_2653_, 2, v_options_2635_);
                leanh::lean_ctor_set(v___x_2653_, 3, v_currRecDepth_2636_);
                leanh::lean_ctor_set(v___x_2653_, 4, v_maxRecDepth_2637_);
                leanh::lean_ctor_set(v___x_2653_, 5, v_ref_2652_);
                leanh::lean_ctor_set(v___x_2653_, 6, v_currNamespace_2639_);
                leanh::lean_ctor_set(v___x_2653_, 7, v_openDecls_2640_);
                leanh::lean_ctor_set(v___x_2653_, 8, v_initHeartbeats_2641_);
                leanh::lean_ctor_set(v___x_2653_, 9, v_maxHeartbeats_2642_);
                leanh::lean_ctor_set(v___x_2653_, 10, v_quotContext_2643_);
                leanh::lean_ctor_set(v___x_2653_, 11, v_currMacroScope_2644_);
                leanh::lean_ctor_set(v___x_2653_, 12, v_cancelTk_x3f_2646_);
                leanh::lean_ctor_set(v___x_2653_, 13, v_inheritedTraceOptions_2648_);
                leanh::lean_ctor_set_uint8(
                    v___x_2653_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2645_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2653_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2647_,
                );
                v___x_2654_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2651_);
                leanh::lean_dec_ref(v_traces_2651_);
                v_sz_2655_ = lean_array_size(v___x_2654_);
                v___x_2656_ = 0usize;
                v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__8(v_sz_2655_, v___x_2656_, v___x_2654_);
                v_msg_2658_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v_msg_2658_, 0, v_data_2625_);
                leanh::lean_ctor_set(v_msg_2658_, 1, v_msg_2627_);
                leanh::lean_ctor_set(v_msg_2658_, 2, v___x_2657_);
                v___x_2659_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6_spec__9(v_msg_2658_, v___y_2628_, v___y_2629_, v___x_2653_, v___y_2631_);
                leanh::lean_dec_ref_known(v___x_2653_, 14);
                v_a_2660_ = leanh::lean_ctor_get(v___x_2659_, 0);
                v_isSharedCheck_2697_ = (!leanh::lean_is_exclusive(v___x_2659_)) as u8;
                if v_isSharedCheck_2697_ == 0 {
                    v___x_2662_ = v___x_2659_;
                    v_isShared_2663_ = v_isSharedCheck_2697_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2660_);
                    leanh::lean_dec(v___x_2659_);
                    v___x_2662_ = leanh::lean_box(0);
                    v_isShared_2663_ = v_isSharedCheck_2697_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2664_ = lean_st_ref_take(v___y_2631_);
                v_traceState_2665_ = leanh::lean_ctor_get(v___x_2664_, 4);
                v_env_2666_ = leanh::lean_ctor_get(v___x_2664_, 0);
                v_nextMacroScope_2667_ = leanh::lean_ctor_get(v___x_2664_, 1);
                v_ngen_2668_ = leanh::lean_ctor_get(v___x_2664_, 2);
                v_auxDeclNGen_2669_ = leanh::lean_ctor_get(v___x_2664_, 3);
                v_cache_2670_ = leanh::lean_ctor_get(v___x_2664_, 5);
                v_messages_2671_ = leanh::lean_ctor_get(v___x_2664_, 6);
                v_infoState_2672_ = leanh::lean_ctor_get(v___x_2664_, 7);
                v_snapshotTasks_2673_ = leanh::lean_ctor_get(v___x_2664_, 8);
                v_isSharedCheck_2696_ = (!leanh::lean_is_exclusive(v___x_2664_)) as u8;
                if v_isSharedCheck_2696_ == 0 {
                    v___x_2675_ = v___x_2664_;
                    v_isShared_2676_ = v_isSharedCheck_2696_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2673_);
                    leanh::lean_inc(v_infoState_2672_);
                    leanh::lean_inc(v_messages_2671_);
                    leanh::lean_inc(v_cache_2670_);
                    leanh::lean_inc(v_traceState_2665_);
                    leanh::lean_inc(v_auxDeclNGen_2669_);
                    leanh::lean_inc(v_ngen_2668_);
                    leanh::lean_inc(v_nextMacroScope_2667_);
                    leanh::lean_inc(v_env_2666_);
                    leanh::lean_dec(v___x_2664_);
                    v___x_2675_ = leanh::lean_box(0);
                    v_isShared_2676_ = v_isSharedCheck_2696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2677_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2665_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2694_ =
                    (!leanh::lean_is_exclusive(v_traceState_2665_)) as u8;
                if v_isSharedCheck_2694_ == 0 {
                    v_unused_2695_ = leanh::lean_ctor_get(v_traceState_2665_, 0);
                    leanh::lean_dec(v_unused_2695_);
                    v___x_2679_ = v_traceState_2665_;
                    v_isShared_2680_ = v_isSharedCheck_2694_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_2665_);
                    v___x_2679_ = leanh::lean_box(0);
                    v_isShared_2680_ = v_isSharedCheck_2694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2681_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2681_, 0, v_ref_2626_);
                leanh::lean_ctor_set(v___x_2681_, 1, v_a_2660_);
                v___x_2682_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2624_, v___x_2681_);
                if v_isShared_2680_ == 0 {
                    leanh::lean_ctor_set(v___x_2679_, 0, v___x_2682_);
                    v___x_2684_ = v___x_2679_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2682_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2693_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2677_,
                    );
                    v___x_2684_ = v_reuseFailAlloc_2693_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2676_ == 0 {
                    leanh::lean_ctor_set(v___x_2675_, 4, v___x_2684_);
                    v___x_2686_ = v___x_2675_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_env_2666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_nextMacroScope_2667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_ngen_2668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_auxDeclNGen_2669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 4, v___x_2684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 5, v_cache_2670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 6, v_messages_2671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 7, v_infoState_2672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 8, v_snapshotTasks_2673_);
                    v___x_2686_ = v_reuseFailAlloc_2692_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2687_ = lean_st_ref_set(v___y_2631_, v___x_2686_);
                v___x_2688_ = leanh::lean_box(0);
                if v_isShared_2663_ == 0 {
                    leanh::lean_ctor_set(v___x_2662_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2662_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6___boxed(
    mut v_oldTraces_2698_: *mut leanh::LeanObject,
    mut v_data_2699_: *mut leanh::LeanObject,
    mut v_ref_2700_: *mut leanh::LeanObject,
    mut v_msg_2701_: *mut leanh::LeanObject,
    mut v___y_2702_: *mut leanh::LeanObject,
    mut v___y_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6(v_oldTraces_2698_, v_data_2699_, v_ref_2700_, v_msg_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
    leanh::lean_dec(v___y_2705_);
    leanh::lean_dec_ref(v___y_2704_);
    leanh::lean_dec(v___y_2703_);
    leanh::lean_dec_ref(v___y_2702_);
    return v_res_2707_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__8(
    mut v_opts_2708_: *mut leanh::LeanObject,
    mut v_opt_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2710_ = leanh::lean_ctor_get(v_opt_2709_, 0);
    v_defValue_2711_ = leanh::lean_ctor_get(v_opt_2709_, 1);
    v_map_2712_ = leanh::lean_ctor_get(v_opts_2708_, 0);
    v___x_2713_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2712_,
            v_name_2710_,
        );
    if leanh::lean_obj_tag(v___x_2713_) == 0 {
        leanh::lean_inc(v_defValue_2711_);
        return v_defValue_2711_;
    } else {
        let mut v_val_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2714_ = leanh::lean_ctor_get(v___x_2713_, 0);
        leanh::lean_inc(v_val_2714_);
        leanh::lean_dec_ref_known(v___x_2713_, 1);
        if leanh::lean_obj_tag(v_val_2714_) == 3 {
            let mut v_v_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_2715_ = leanh::lean_ctor_get(v_val_2714_, 0);
            leanh::lean_inc(v_v_2715_);
            leanh::lean_dec_ref_known(v_val_2714_, 1);
            return v_v_2715_;
        } else {
            leanh::lean_dec(v_val_2714_);
            leanh::lean_inc(v_defValue_2711_);
            return v_defValue_2711_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__8___boxed(
    mut v_opts_2716_: *mut leanh::LeanObject,
    mut v_opt_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__8(v_opts_2716_, v_opt_2717_);
    leanh::lean_dec_ref(v_opt_2717_);
    leanh::lean_dec_ref(v_opts_2716_);
    return v_res_2718_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__0;
    v___x_2721_ = l_Lean_stringToMessageData(v___x_2720_);
    return v___x_2721_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__2()
-> f64 {
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: f64 = 0.0;
    v___x_2722_ = leanh::lean_unsigned_to_nat(0);
    v___x_2723_ = lean_float_of_nat(v___x_2722_);
    return v___x_2723_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__3;
    v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
    return v___x_2726_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__5()
-> f64 {
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: f64 = 0.0;
    v___x_2727_ = leanh::lean_unsigned_to_nat(1000);
    v___x_2728_ = lean_float_of_nat(v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4(
    mut v_cls_2729_: *mut leanh::LeanObject,
    mut v_collapsed_2730_: u8,
    mut v_tag_2731_: *mut leanh::LeanObject,
    mut v_opts_2732_: *mut leanh::LeanObject,
    mut v_clsEnabled_2733_: u8,
    mut v_oldTraces_2734_: *mut leanh::LeanObject,
    mut v_msg_2735_: *mut leanh::LeanObject,
    mut v_resStartStop_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v___y_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2746_: u8 = 0;
    let mut v___y_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut v_fst_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2765_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u8 = 0;
    let mut v___y_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2771_: u8 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: f64 = 0.0;
    let mut v_data_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: f64 = 0.0;
    let mut v___x_2785_: f64 = 0.0;
    let mut v_reuseFailAlloc_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2794_: u8 = 0;
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2807_: u8 = 0;
    let mut v_tid_2808_: u64 = 0;
    let mut v_traces_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v___y_2825_: f64 = 0.0;
    let mut v___x_2826_: f64 = 0.0;
    let mut v___x_2827_: f64 = 0.0;
    let mut v___x_2828_: f64 = 0.0;
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: f64 = 0.0;
    let mut v___x_2835_: f64 = 0.0;
    let mut v___x_2836_: f64 = 0.0;
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: f64 = 0.0;
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2742_ = leanh::lean_ctor_get(v_resStartStop_2736_, 0);
                v_snd_2743_ = leanh::lean_ctor_get(v_resStartStop_2736_, 1);
                v_isSharedCheck_2841_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_2736_)) as u8;
                if v_isSharedCheck_2841_ == 0 {
                    v___x_2745_ = v_resStartStop_2736_;
                    v_isShared_2746_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2743_);
                    leanh::lean_inc(v_fst_2742_);
                    leanh::lean_dec(v_resStartStop_2736_);
                    v___x_2745_ = leanh::lean_box(0);
                    v_isShared_2746_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2761_ = leanh::lean_ctor_get(v_snd_2743_, 0);
                v_snd_2762_ = leanh::lean_ctor_get(v_snd_2743_, 1);
                v_isSharedCheck_2840_ = (!leanh::lean_is_exclusive(v_snd_2743_)) as u8;
                if v_isSharedCheck_2840_ == 0 {
                    v___x_2764_ = v_snd_2743_;
                    v_isShared_2765_ = v_isSharedCheck_2840_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2762_);
                    leanh::lean_inc(v_fst_2761_);
                    leanh::lean_dec(v_snd_2743_);
                    v___x_2764_ = leanh::lean_box(0);
                    v_isShared_2765_ = v_isSharedCheck_2840_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_2748_);
                v___x_2751_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__6(v_oldTraces_2734_, v_data_2750_, v___y_2748_, v___y_2749_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
                if leanh::lean_obj_tag(v___x_2751_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2751_, 1);
                    v___x_2752_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7___redArg(v_fst_2742_);
                    return v___x_2752_;
                } else {
                    leanh::lean_dec(v_fst_2742_);
                    v_a_2753_ = leanh::lean_ctor_get(v___x_2751_, 0);
                    v_isSharedCheck_2760_ = (!leanh::lean_is_exclusive(v___x_2751_)) as u8;
                    if v_isSharedCheck_2760_ == 0 {
                        v___x_2755_ = v___x_2751_;
                        v_isShared_2756_ = v_isSharedCheck_2760_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2753_);
                        leanh::lean_dec(v___x_2751_);
                        v___x_2755_ = leanh::lean_box(0);
                        v_isShared_2756_ = v_isSharedCheck_2760_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2756_ == 0 {
                    v___x_2758_ = v___x_2755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
                    v___x_2758_ = v_reuseFailAlloc_2759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2758_;
            }
            5 => {
                v___x_2766_ = l_Lean_trace_profiler;
                v___x_2767_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__3(v_opts_2732_, v___x_2766_);
                if v___x_2767_ == 0 {
                    v___y_2794_ = v___x_2767_;
                    state = 10;
                    continue;
                } else {
                    v___x_2830_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_2831_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__3(v_opts_2732_, v___x_2830_);
                    if v___x_2831_ == 0 {
                        v___x_2832_ = l_Lean_trace_profiler_threshold;
                        v___x_2833_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__8(v_opts_2732_, v___x_2832_);
                        v___x_2834_ = lean_float_of_nat(v___x_2833_);
                        v___x_2835_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__5);
                        v___x_2836_ = lean_float_div(v___x_2834_, v___x_2835_);
                        v___y_2825_ = v___x_2836_;
                        state = 15;
                        continue;
                    } else {
                        v___x_2837_ = l_Lean_trace_profiler_threshold;
                        v___x_2838_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__8(v_opts_2732_, v___x_2837_);
                        v___x_2839_ = lean_float_of_nat(v___x_2838_);
                        v___y_2825_ = v___x_2839_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_2771_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__5(v_fst_2742_);
                v___x_2772_ = l_Lean_TraceResult_toEmoji(v_result_2771_);
                v___x_2773_ = l_Lean_stringToMessageData(v___x_2772_);
                v___x_2774_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__1);
                if v_isShared_2765_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2764_, 7);
                    leanh::lean_ctor_set(v___x_2764_, 1, v___x_2774_);
                    leanh::lean_ctor_set(v___x_2764_, 0, v___x_2773_);
                    v___x_2776_ = v___x_2764_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2774_);
                    v___x_2776_ = v_reuseFailAlloc_2787_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2746_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2745_, 7);
                    leanh::lean_ctor_set(v___x_2745_, 1, v_a_2770_);
                    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2776_);
                    v_m_2778_ = v___x_2745_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_a_2770_);
                    v_m_2778_ = v_reuseFailAlloc_2786_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2779_ = leanh::lean_box((v_result_2771_) as usize);
                v___x_2780_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2780_, 0, v___x_2779_);
                v___x_2781_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__2);
                leanh::lean_inc_ref(v_tag_2731_);
                leanh::lean_inc_ref(v___x_2780_);
                leanh::lean_inc(v_cls_2729_);
                v_data_2782_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_2782_, 0, v_cls_2729_);
                leanh::lean_ctor_set(v_data_2782_, 1, v___x_2780_);
                leanh::lean_ctor_set(v_data_2782_, 2, v_tag_2731_);
                leanh::lean_ctor_set_float(
                    v_data_2782_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2781_,
                );
                leanh::lean_ctor_set_float(
                    v_data_2782_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2781_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_2782_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_2730_,
                );
                if v___x_2767_ == 0 {
                    leanh::lean_dec_ref_known(v___x_2780_, 1);
                    leanh::lean_dec(v_snd_2762_);
                    leanh::lean_dec(v_fst_2761_);
                    leanh::lean_dec_ref(v_tag_2731_);
                    leanh::lean_dec(v_cls_2729_);
                    v___y_2748_ = v___y_2769_;
                    v___y_2749_ = v_m_2778_;
                    v_data_2750_ = v_data_2782_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_2782_, 3);
                    v_data_2783_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_2783_, 0, v_cls_2729_);
                    leanh::lean_ctor_set(v_data_2783_, 1, v___x_2780_);
                    leanh::lean_ctor_set(v_data_2783_, 2, v_tag_2731_);
                    v___x_2784_ = leanh::lean_unbox_float(v_fst_2761_);
                    leanh::lean_dec(v_fst_2761_);
                    leanh::lean_ctor_set_float(
                        v_data_2783_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_2784_,
                    );
                    v___x_2785_ = leanh::lean_unbox_float(v_snd_2762_);
                    leanh::lean_dec(v_snd_2762_);
                    leanh::lean_ctor_set_float(
                        v_data_2783_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_2785_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_2783_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_2730_,
                    );
                    v___y_2748_ = v___y_2769_;
                    v___y_2749_ = v_m_2778_;
                    v_data_2750_ = v_data_2783_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_2789_ = leanh::lean_ctor_get(v___y_2739_, 5);
                leanh::lean_inc(v___y_2740_);
                leanh::lean_inc_ref(v___y_2739_);
                leanh::lean_inc(v___y_2738_);
                leanh::lean_inc_ref(v___y_2737_);
                leanh::lean_inc(v_fst_2742_);
                v___x_2790_ = leanh::lean_apply_6(
                    v_msg_2735_,
                    v_fst_2742_,
                    v___y_2737_,
                    v___y_2738_,
                    v___y_2739_,
                    v___y_2740_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2790_) == 0 {
                    v_a_2791_ = leanh::lean_ctor_get(v___x_2790_, 0);
                    leanh::lean_inc(v_a_2791_);
                    leanh::lean_dec_ref_known(v___x_2790_, 1);
                    v___y_2769_ = v_ref_2789_;
                    v_a_2770_ = v_a_2791_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_2790_, 1);
                    v___x_2792_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___closed__4);
                    v___y_2769_ = v_ref_2789_;
                    v_a_2770_ = v___x_2792_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_2733_ == 0 {
                    if v___y_2794_ == 0 {
                        leanh::lean_del_object(v___x_2764_);
                        leanh::lean_dec(v_snd_2762_);
                        leanh::lean_dec(v_fst_2761_);
                        leanh::lean_del_object(v___x_2745_);
                        leanh::lean_dec_ref(v_msg_2735_);
                        leanh::lean_dec_ref(v_tag_2731_);
                        leanh::lean_dec(v_cls_2729_);
                        v___x_2795_ = lean_st_ref_take(v___y_2740_);
                        v_traceState_2796_ = leanh::lean_ctor_get(v___x_2795_, 4);
                        v_env_2797_ = leanh::lean_ctor_get(v___x_2795_, 0);
                        v_nextMacroScope_2798_ = leanh::lean_ctor_get(v___x_2795_, 1);
                        v_ngen_2799_ = leanh::lean_ctor_get(v___x_2795_, 2);
                        v_auxDeclNGen_2800_ = leanh::lean_ctor_get(v___x_2795_, 3);
                        v_cache_2801_ = leanh::lean_ctor_get(v___x_2795_, 5);
                        v_messages_2802_ = leanh::lean_ctor_get(v___x_2795_, 6);
                        v_infoState_2803_ = leanh::lean_ctor_get(v___x_2795_, 7);
                        v_snapshotTasks_2804_ = leanh::lean_ctor_get(v___x_2795_, 8);
                        v_isSharedCheck_2823_ =
                            (!leanh::lean_is_exclusive(v___x_2795_)) as u8;
                        if v_isSharedCheck_2823_ == 0 {
                            v___x_2806_ = v___x_2795_;
                            v_isShared_2807_ = v_isSharedCheck_2823_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_2804_);
                            leanh::lean_inc(v_infoState_2803_);
                            leanh::lean_inc(v_messages_2802_);
                            leanh::lean_inc(v_cache_2801_);
                            leanh::lean_inc(v_traceState_2796_);
                            leanh::lean_inc(v_auxDeclNGen_2800_);
                            leanh::lean_inc(v_ngen_2799_);
                            leanh::lean_inc(v_nextMacroScope_2798_);
                            leanh::lean_inc(v_env_2797_);
                            leanh::lean_dec(v___x_2795_);
                            v___x_2806_ = leanh::lean_box(0);
                            v_isShared_2807_ = v_isSharedCheck_2823_;
                            state = 11;
                            continue;
                        }
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_tid_2808_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2809_ = leanh::lean_ctor_get(v_traceState_2796_, 0);
                v_isSharedCheck_2822_ =
                    (!leanh::lean_is_exclusive(v_traceState_2796_)) as u8;
                if v_isSharedCheck_2822_ == 0 {
                    v___x_2811_ = v_traceState_2796_;
                    v_isShared_2812_ = v_isSharedCheck_2822_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_2809_);
                    leanh::lean_dec(v_traceState_2796_);
                    v___x_2811_ = leanh::lean_box(0);
                    v_isShared_2812_ = v_isSharedCheck_2822_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2813_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_2734_, v_traces_2809_);
                leanh::lean_dec_ref(v_traces_2809_);
                if v_isShared_2812_ == 0 {
                    leanh::lean_ctor_set(v___x_2811_, 0, v___x_2813_);
                    v___x_2815_ = v___x_2811_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2821_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2813_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2821_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2808_,
                    );
                    v___x_2815_ = v_reuseFailAlloc_2821_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2807_ == 0 {
                    leanh::lean_ctor_set(v___x_2806_, 4, v___x_2815_);
                    v___x_2817_ = v___x_2806_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2820_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_env_2797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_nextMacroScope_2798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 2, v_ngen_2799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 3, v_auxDeclNGen_2800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 4, v___x_2815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 5, v_cache_2801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 6, v_messages_2802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 7, v_infoState_2803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 8, v_snapshotTasks_2804_);
                    v___x_2817_ = v_reuseFailAlloc_2820_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2818_ = lean_st_ref_set(v___y_2740_, v___x_2817_);
                v___x_2819_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7___redArg(v_fst_2742_);
                return v___x_2819_;
            }
            15 => {
                v___x_2826_ = leanh::lean_unbox_float(v_snd_2762_);
                v___x_2827_ = leanh::lean_unbox_float(v_fst_2761_);
                v___x_2828_ = lean_float_sub(v___x_2826_, v___x_2827_);
                v___x_2829_ = lean_float_decLt(v___y_2825_, v___x_2828_);
                v___y_2794_ = v___x_2829_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4___boxed(
    mut v_cls_2842_: *mut leanh::LeanObject,
    mut v_collapsed_2843_: *mut leanh::LeanObject,
    mut v_tag_2844_: *mut leanh::LeanObject,
    mut v_opts_2845_: *mut leanh::LeanObject,
    mut v_clsEnabled_2846_: *mut leanh::LeanObject,
    mut v_oldTraces_2847_: *mut leanh::LeanObject,
    mut v_msg_2848_: *mut leanh::LeanObject,
    mut v_resStartStop_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
    mut v___y_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_2855_: u8 = 0;
    let mut v_clsEnabled_boxed_2856_: u8 = 0;
    let mut v_res_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_2855_ = (leanh::lean_unbox(v_collapsed_2843_) as u8);
    v_clsEnabled_boxed_2856_ = (leanh::lean_unbox(v_clsEnabled_2846_) as u8);
    v_res_2857_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4(v_cls_2842_, v_collapsed_boxed_2855_, v_tag_2844_, v_opts_2845_, v_clsEnabled_boxed_2856_, v_oldTraces_2847_, v_msg_2848_, v_resStartStop_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
    leanh::lean_dec(v___y_2853_);
    leanh::lean_dec_ref(v___y_2852_);
    leanh::lean_dec(v___y_2851_);
    leanh::lean_dec_ref(v___y_2850_);
    leanh::lean_dec_ref(v_opts_2845_);
    return v_res_2857_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__1(
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2858_) == 0 {
                    v___x_2860_ = l_List_reverse___redArg(v_a_2859_);
                    return v___x_2860_;
                } else {
                    v_head_2861_ = leanh::lean_ctor_get(v_a_2858_, 0);
                    v_tail_2862_ = leanh::lean_ctor_get(v_a_2858_, 1);
                    v_isSharedCheck_2871_ = (!leanh::lean_is_exclusive(v_a_2858_)) as u8;
                    if v_isSharedCheck_2871_ == 0 {
                        v___x_2864_ = v_a_2858_;
                        v_isShared_2865_ = v_isSharedCheck_2871_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2862_);
                        leanh::lean_inc(v_head_2861_);
                        leanh::lean_dec(v_a_2858_);
                        v___x_2864_ = leanh::lean_box(0);
                        v_isShared_2865_ = v_isSharedCheck_2871_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2866_ = l_Lean_mkLevelParam(v_head_2861_);
                if v_isShared_2865_ == 0 {
                    leanh::lean_ctor_set(v___x_2864_, 1, v_a_2859_);
                    leanh::lean_ctor_set(v___x_2864_, 0, v___x_2866_);
                    v___x_2868_ = v___x_2864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2870_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_a_2859_);
                    v___x_2868_ = v_reuseFailAlloc_2870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2858_ = v_tail_2862_;
                v_a_2859_ = v___x_2868_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__2;
    v___x_2881_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__5;
    v___x_2882_ = l_Lean_Name_append(v___x_2881_, v___x_2880_);
    return v___x_2882_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__7()
-> f64 {
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: f64 = 0.0;
    v___x_2883_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_2884_ = lean_float_of_nat(v___x_2883_);
    return v___x_2884_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem(
    mut v_declName_2885_: *mut leanh::LeanObject,
    mut v_a_2886_: *mut leanh::LeanObject,
    mut v_a_2887_: *mut leanh::LeanObject,
    mut v_a_2888_: *mut leanh::LeanObject,
    mut v_a_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2898_: u8 = 0;
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v_val_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2919_: u8 = 0;
    let mut v_toConstantVal_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2923_: u8 = 0;
    let mut v_levelParams_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2951_: u8 = 0;
    let mut v_unused_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_reuseFailAlloc_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v_unused_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2966_: u8 = 0;
    let mut v_unused_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_inheritedTraceOptions_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___y_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: f64 = 0.0;
    let mut v___x_2984_: f64 = 0.0;
    let mut v___x_2985_: f64 = 0.0;
    let mut v___x_2986_: f64 = 0.0;
    let mut v___x_2987_: f64 = 0.0;
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: f64 = 0.0;
    let mut v___x_3015_: f64 = 0.0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v_val_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v_toConstantVal_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v_levelParams_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v_unused_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3095_: u8 = 0;
    let mut v_unused_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_unused_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: u8 = 0;
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v_val_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v_toConstantVal_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v_levelParams_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v_unused_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v_unused_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3162_: u8 = 0;
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut v_unused_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u8 = 0;
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v_val_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v_toConstantVal_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v_levelParams_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_unused_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_reuseFailAlloc_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3238_: u8 = 0;
    let mut v_unused_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3241_: u8 = 0;
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2897_ = leanh::lean_ctor_get(v_a_2888_, 2);
                v_hasTrace_2898_ = leanh::lean_ctor_get_uint8(
                    v_options_2897_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_2898_ == 0 {
                    v___x_2899_ = lean_st_ref_get(v_a_2889_);
                    v_env_2900_ = leanh::lean_ctor_get(v___x_2899_, 0);
                    leanh::lean_inc_ref(v_env_2900_);
                    leanh::lean_dec(v___x_2899_);
                    v___x_2901_ = l_Lean_Meta_unfoldThmSuffix;
                    leanh::lean_inc_n(v_declName_2885_, 2);
                    v___x_2902_ =
                        l_Lean_Meta_mkEqLikeNameFor(v_env_2900_, v_declName_2885_, v___x_2901_);
                    v___x_2903_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0(v_declName_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                    if leanh::lean_obj_tag(v___x_2903_) == 0 {
                        v_a_2904_ = leanh::lean_ctor_get(v___x_2903_, 0);
                        leanh::lean_inc(v_a_2904_);
                        leanh::lean_dec_ref_known(v___x_2903_, 1);
                        if leanh::lean_obj_tag(v_a_2904_) == 1 {
                            v_val_2905_ = leanh::lean_ctor_get(v_a_2904_, 0);
                            leanh::lean_inc(v_val_2905_);
                            leanh::lean_dec_ref_known(v_a_2904_, 1);
                            v___x_2906_ = lean_st_ref_get(v_a_2889_);
                            v_env_2907_ = leanh::lean_ctor_get(v___x_2906_, 0);
                            leanh::lean_inc_ref(v_env_2907_);
                            leanh::lean_dec(v___x_2906_);
                            leanh::lean_inc(v_declName_2885_);
                            v___x_2908_ = l_Lean_privateToUserName(v_declName_2885_);
                            v___x_2909_ = l_Lean_Name_str___override(v___x_2908_, v___x_2901_);
                            v___x_2910_ = l_Lean_mkPrivateNameCore(v_val_2905_, v___x_2909_);
                            leanh::lean_inc(v___x_2910_);
                            v___x_2911_ = l_Lean_Environment_find_x3f(
                                v_env_2907_,
                                v___x_2910_,
                                v_hasTrace_2898_,
                            );
                            if leanh::lean_obj_tag(v___x_2911_) == 1 {
                                v_val_2912_ = leanh::lean_ctor_get(v___x_2911_, 0);
                                v_isSharedCheck_2970_ =
                                    (!leanh::lean_is_exclusive(v___x_2911_)) as u8;
                                if v_isSharedCheck_2970_ == 0 {
                                    v___x_2914_ = v___x_2911_;
                                    v_isShared_2915_ = v_isSharedCheck_2970_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_2912_);
                                    leanh::lean_dec(v___x_2911_);
                                    v___x_2914_ = leanh::lean_box(0);
                                    v_isShared_2915_ = v_isSharedCheck_2970_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_2911_);
                                leanh::lean_dec(v___x_2910_);
                                leanh::lean_dec(v___x_2902_);
                                leanh::lean_dec(v_declName_2885_);
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2904_);
                            leanh::lean_dec(v___x_2902_);
                            leanh::lean_dec(v_declName_2885_);
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2902_);
                        leanh::lean_dec(v_declName_2885_);
                        return v___x_2903_;
                    }
                } else {
                    v_inheritedTraceOptions_2971_ = leanh::lean_ctor_get(v_a_2888_, 13);
                    leanh::lean_inc(v_declName_2885_);
                    v___f_2972_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__1___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_2972_, 0, v_declName_2885_);
                    v___f_2973_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__0;
                    v___x_2974_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__2;
                    v___x_2975_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__3;
                    v___x_2976_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__6);
                    v___x_2977_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2971_,
                        v_options_2897_,
                        v___x_2976_,
                    );
                    if v___x_2977_ == 0 {
                        v___x_3169_ = l_Lean_trace_profiler;
                        v___x_3170_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__3(v_options_2897_, v___x_3169_);
                        if v___x_3170_ == 0 {
                            leanh::lean_dec_ref(v___f_2972_);
                            v___x_3171_ = lean_st_ref_get(v_a_2889_);
                            v_env_3172_ = leanh::lean_ctor_get(v___x_3171_, 0);
                            leanh::lean_inc_ref(v_env_3172_);
                            leanh::lean_dec(v___x_3171_);
                            v___x_3173_ = l_Lean_Meta_unfoldThmSuffix;
                            leanh::lean_inc_n(v_declName_2885_, 2);
                            v___x_3174_ = l_Lean_Meta_mkEqLikeNameFor(
                                v_env_3172_,
                                v_declName_2885_,
                                v___x_3173_,
                            );
                            v___x_3175_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0(v_declName_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                            if leanh::lean_obj_tag(v___x_3175_) == 0 {
                                v_a_3176_ = leanh::lean_ctor_get(v___x_3175_, 0);
                                leanh::lean_inc(v_a_3176_);
                                leanh::lean_dec_ref_known(v___x_3175_, 1);
                                if leanh::lean_obj_tag(v_a_3176_) == 1 {
                                    v_val_3177_ = leanh::lean_ctor_get(v_a_3176_, 0);
                                    leanh::lean_inc(v_val_3177_);
                                    leanh::lean_dec_ref_known(v_a_3176_, 1);
                                    v___x_3178_ = lean_st_ref_get(v_a_2889_);
                                    v_env_3179_ = leanh::lean_ctor_get(v___x_3178_, 0);
                                    leanh::lean_inc_ref(v_env_3179_);
                                    leanh::lean_dec(v___x_3178_);
                                    leanh::lean_inc(v_declName_2885_);
                                    v___x_3180_ = l_Lean_privateToUserName(v_declName_2885_);
                                    v___x_3181_ =
                                        l_Lean_Name_str___override(v___x_3180_, v___x_3173_);
                                    v___x_3182_ =
                                        l_Lean_mkPrivateNameCore(v_val_3177_, v___x_3181_);
                                    leanh::lean_inc(v___x_3182_);
                                    v___x_3183_ = l_Lean_Environment_find_x3f(
                                        v_env_3179_,
                                        v___x_3182_,
                                        v___x_3170_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3183_) == 1 {
                                        v_val_3184_ = leanh::lean_ctor_get(v___x_3183_, 0);
                                        v_isSharedCheck_3242_ =
                                            (!leanh::lean_is_exclusive(v___x_3183_)) as u8;
                                        if v_isSharedCheck_3242_ == 0 {
                                            v___x_3186_ = v___x_3183_;
                                            v_isShared_3187_ = v_isSharedCheck_3242_;
                                            state = 40;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_val_3184_);
                                            leanh::lean_dec(v___x_3183_);
                                            v___x_3186_ = leanh::lean_box(0);
                                            v_isShared_3187_ = v_isSharedCheck_3242_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v___x_3183_);
                                        leanh::lean_dec(v___x_3182_);
                                        leanh::lean_dec(v___x_3174_);
                                        leanh::lean_dec(v_declName_2885_);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3176_);
                                    leanh::lean_dec(v___x_3174_);
                                    leanh::lean_dec(v_declName_2885_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_3174_);
                                leanh::lean_dec(v_declName_2885_);
                                return v___x_3175_;
                            }
                        } else {
                            state = 23;
                            continue;
                        }
                    } else {
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2892_ = leanh::lean_box(0);
                v___x_2893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2893_, 0, v___x_2892_);
                return v___x_2893_;
            }
            2 => {
                v___x_2895_ = leanh::lean_box(0);
                v___x_2896_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2896_, 0, v___x_2895_);
                return v___x_2896_;
            }
            3 => {
                if leanh::lean_obj_tag(v_val_2912_) == 2 {
                    v_val_2916_ = leanh::lean_ctor_get(v_val_2912_, 0);
                    v_isSharedCheck_2969_ = (!leanh::lean_is_exclusive(v_val_2912_)) as u8;
                    if v_isSharedCheck_2969_ == 0 {
                        v___x_2918_ = v_val_2912_;
                        v_isShared_2919_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2916_);
                        leanh::lean_dec(v_val_2912_);
                        v___x_2918_ = leanh::lean_box(0);
                        v_isShared_2919_ = v_isSharedCheck_2969_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2914_);
                    leanh::lean_dec(v_val_2912_);
                    leanh::lean_dec(v___x_2910_);
                    leanh::lean_dec(v___x_2902_);
                    leanh::lean_dec(v_declName_2885_);
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_toConstantVal_2920_ = leanh::lean_ctor_get(v_val_2916_, 0);
                v_isSharedCheck_2966_ = (!leanh::lean_is_exclusive(v_val_2916_)) as u8;
                if v_isSharedCheck_2966_ == 0 {
                    v_unused_2967_ = leanh::lean_ctor_get(v_val_2916_, 2);
                    leanh::lean_dec(v_unused_2967_);
                    v_unused_2968_ = leanh::lean_ctor_get(v_val_2916_, 1);
                    leanh::lean_dec(v_unused_2968_);
                    v___x_2922_ = v_val_2916_;
                    v_isShared_2923_ = v_isSharedCheck_2966_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toConstantVal_2920_);
                    leanh::lean_dec(v_val_2916_);
                    v___x_2922_ = leanh::lean_box(0);
                    v_isShared_2923_ = v_isSharedCheck_2966_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_levelParams_2924_ = leanh::lean_ctor_get(v_toConstantVal_2920_, 1);
                v_type_2925_ = leanh::lean_ctor_get(v_toConstantVal_2920_, 2);
                v_isSharedCheck_2964_ =
                    (!leanh::lean_is_exclusive(v_toConstantVal_2920_)) as u8;
                if v_isSharedCheck_2964_ == 0 {
                    v_unused_2965_ = leanh::lean_ctor_get(v_toConstantVal_2920_, 0);
                    leanh::lean_dec(v_unused_2965_);
                    v___x_2927_ = v_toConstantVal_2920_;
                    v_isShared_2928_ = v_isSharedCheck_2964_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_type_2925_);
                    leanh::lean_inc(v_levelParams_2924_);
                    leanh::lean_dec(v_toConstantVal_2920_);
                    v___x_2927_ = leanh::lean_box(0);
                    v_isShared_2928_ = v_isSharedCheck_2964_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_levelParams_2924_);
                leanh::lean_inc(v___x_2902_);
                if v_isShared_2928_ == 0 {
                    leanh::lean_ctor_set(v___x_2927_, 0, v___x_2902_);
                    v___x_2930_ = v___x_2927_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_levelParams_2924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_type_2925_);
                    v___x_2930_ = v_reuseFailAlloc_2963_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2931_ = leanh::lean_box(0);
                v___x_2932_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__1(v_levelParams_2924_, v___x_2931_);
                v___x_2933_ = l_Lean_Expr_const___override(v___x_2910_, v___x_2932_);
                leanh::lean_inc(v___x_2902_);
                v___x_2934_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2934_, 0, v___x_2902_);
                leanh::lean_ctor_set(v___x_2934_, 1, v___x_2931_);
                if v_isShared_2923_ == 0 {
                    leanh::lean_ctor_set(v___x_2922_, 2, v___x_2934_);
                    leanh::lean_ctor_set(v___x_2922_, 1, v___x_2933_);
                    leanh::lean_ctor_set(v___x_2922_, 0, v___x_2930_);
                    v___x_2936_ = v___x_2922_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 1, v___x_2933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 2, v___x_2934_);
                    v___x_2936_ = v_reuseFailAlloc_2962_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2919_ == 0 {
                    leanh::lean_ctor_set(v___x_2918_, 0, v___x_2936_);
                    v___x_2938_ = v___x_2918_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2961_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2936_);
                    v___x_2938_ = v_reuseFailAlloc_2961_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2939_ = leanh::lean_box((v_hasTrace_2898_) as usize);
                v___f_2940_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                leanh::lean_closure_set(v___f_2940_, 0, v___x_2938_);
                leanh::lean_closure_set(v___f_2940_, 1, v___x_2939_);
                leanh::lean_inc(v___x_2902_);
                v___x_2941_ = l_Lean_Meta_realizeConst(
                    v_declName_2885_,
                    v___x_2902_,
                    v___f_2940_,
                    v_a_2886_,
                    v_a_2887_,
                    v_a_2888_,
                    v_a_2889_,
                );
                if leanh::lean_obj_tag(v___x_2941_) == 0 {
                    v_isSharedCheck_2951_ = (!leanh::lean_is_exclusive(v___x_2941_)) as u8;
                    if v_isSharedCheck_2951_ == 0 {
                        v_unused_2952_ = leanh::lean_ctor_get(v___x_2941_, 0);
                        leanh::lean_dec(v_unused_2952_);
                        v___x_2943_ = v___x_2941_;
                        v_isShared_2944_ = v_isSharedCheck_2951_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2941_);
                        v___x_2943_ = leanh::lean_box(0);
                        v_isShared_2944_ = v_isSharedCheck_2951_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2914_);
                    leanh::lean_dec(v___x_2902_);
                    v_a_2953_ = leanh::lean_ctor_get(v___x_2941_, 0);
                    v_isSharedCheck_2960_ = (!leanh::lean_is_exclusive(v___x_2941_)) as u8;
                    if v_isSharedCheck_2960_ == 0 {
                        v___x_2955_ = v___x_2941_;
                        v_isShared_2956_ = v_isSharedCheck_2960_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2953_);
                        leanh::lean_dec(v___x_2941_);
                        v___x_2955_ = leanh::lean_box(0);
                        v_isShared_2956_ = v_isSharedCheck_2960_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2915_ == 0 {
                    leanh::lean_ctor_set(v___x_2914_, 0, v___x_2902_);
                    v___x_2946_ = v___x_2914_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2950_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2902_);
                    v___x_2946_ = v_reuseFailAlloc_2950_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2944_ == 0 {
                    leanh::lean_ctor_set(v___x_2943_, 0, v___x_2946_);
                    v___x_2948_ = v___x_2943_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2949_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
                    v___x_2948_ = v_reuseFailAlloc_2949_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2948_;
            }
            13 => {
                if v_isShared_2956_ == 0 {
                    v___x_2958_ = v___x_2955_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
                    v___x_2958_ = v_reuseFailAlloc_2959_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2958_;
            }
            15 => {
                v___x_2982_ = lean_io_mono_nanos_now();
                v___x_2983_ = lean_float_of_nat(v___y_2979_);
                v___x_2984_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__7_once), _init_l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___closed__7);
                v___x_2985_ = lean_float_div(v___x_2983_, v___x_2984_);
                v___x_2986_ = lean_float_of_nat(v___x_2982_);
                v___x_2987_ = lean_float_div(v___x_2986_, v___x_2984_);
                v___x_2988_ = leanh::lean_box_float(v___x_2985_);
                v___x_2989_ = leanh::lean_box_float(v___x_2987_);
                v___x_2990_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2990_, 0, v___x_2988_);
                leanh::lean_ctor_set(v___x_2990_, 1, v___x_2989_);
                v___x_2991_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2991_, 0, v_a_2981_);
                leanh::lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                v___x_2992_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4(v___x_2974_, v_hasTrace_2898_, v___x_2975_, v_options_2897_, v___x_2977_, v___y_2980_, v___f_2972_, v___x_2991_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                return v___x_2992_;
            }
            16 => {
                v___x_2997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2997_, 0, v_a_2996_);
                v___y_2979_ = v___y_2994_;
                v___y_2980_ = v___y_2995_;
                v_a_2981_ = v___x_2997_;
                state = 15;
                continue;
            }
            17 => {
                v___x_3002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3002_, 0, v_a_3001_);
                v___y_2979_ = v___y_2999_;
                v___y_2980_ = v___y_3000_;
                v_a_2981_ = v___x_3002_;
                state = 15;
                continue;
            }
            18 => {
                if leanh::lean_obj_tag(v___y_3006_) == 0 {
                    v_a_3007_ = leanh::lean_ctor_get(v___y_3006_, 0);
                    leanh::lean_inc(v_a_3007_);
                    leanh::lean_dec_ref_known(v___y_3006_, 1);
                    v___y_2999_ = v___y_3004_;
                    v___y_3000_ = v___y_3005_;
                    v_a_3001_ = v_a_3007_;
                    state = 17;
                    continue;
                } else {
                    v_a_3008_ = leanh::lean_ctor_get(v___y_3006_, 0);
                    leanh::lean_inc(v_a_3008_);
                    leanh::lean_dec_ref_known(v___y_3006_, 1);
                    v___y_2994_ = v___y_3004_;
                    v___y_2995_ = v___y_3005_;
                    v_a_2996_ = v_a_3008_;
                    state = 16;
                    continue;
                }
            }
            19 => {
                v___x_3013_ = lean_io_get_num_heartbeats();
                v___x_3014_ = lean_float_of_nat(v___y_3011_);
                v___x_3015_ = lean_float_of_nat(v___x_3013_);
                v___x_3016_ = leanh::lean_box_float(v___x_3014_);
                v___x_3017_ = leanh::lean_box_float(v___x_3015_);
                v___x_3018_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3018_, 0, v___x_3016_);
                leanh::lean_ctor_set(v___x_3018_, 1, v___x_3017_);
                v___x_3019_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3019_, 0, v_a_3012_);
                leanh::lean_ctor_set(v___x_3019_, 1, v___x_3018_);
                v___x_3020_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4(v___x_2974_, v_hasTrace_2898_, v___x_2975_, v_options_2897_, v___x_2977_, v___y_3010_, v___f_2972_, v___x_3019_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                return v___x_3020_;
            }
            20 => {
                v___x_3025_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3025_, 0, v_a_3024_);
                v___y_3010_ = v___y_3022_;
                v___y_3011_ = v___y_3023_;
                v_a_3012_ = v___x_3025_;
                state = 19;
                continue;
            }
            21 => {
                v___x_3030_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3030_, 0, v_a_3029_);
                v___y_3010_ = v___y_3027_;
                v___y_3011_ = v___y_3028_;
                v_a_3012_ = v___x_3030_;
                state = 19;
                continue;
            }
            22 => {
                if leanh::lean_obj_tag(v___y_3034_) == 0 {
                    v_a_3035_ = leanh::lean_ctor_get(v___y_3034_, 0);
                    leanh::lean_inc(v_a_3035_);
                    leanh::lean_dec_ref_known(v___y_3034_, 1);
                    v___y_3022_ = v___y_3032_;
                    v___y_3023_ = v___y_3033_;
                    v_a_3024_ = v_a_3035_;
                    state = 20;
                    continue;
                } else {
                    v_a_3036_ = leanh::lean_ctor_get(v___y_3034_, 0);
                    leanh::lean_inc(v_a_3036_);
                    leanh::lean_dec_ref_known(v___y_3034_, 1);
                    v___y_3027_ = v___y_3032_;
                    v___y_3028_ = v___y_3033_;
                    v_a_3029_ = v_a_3036_;
                    state = 21;
                    continue;
                }
            }
            23 => {
                v___x_3038_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__2___redArg(v_a_2889_);
                v_a_3039_ = leanh::lean_ctor_get(v___x_3038_, 0);
                leanh::lean_inc(v_a_3039_);
                leanh::lean_dec_ref(v___x_3038_);
                v___x_3040_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3041_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__3(v_options_2897_, v___x_3040_);
                if v___x_3041_ == 0 {
                    v___x_3042_ = lean_io_mono_nanos_now();
                    v___x_3043_ = lean_st_ref_get(v_a_2889_);
                    v_env_3044_ = leanh::lean_ctor_get(v___x_3043_, 0);
                    leanh::lean_inc_ref(v_env_3044_);
                    leanh::lean_dec(v___x_3043_);
                    v___x_3045_ = l_Lean_Meta_unfoldThmSuffix;
                    leanh::lean_inc_n(v_declName_2885_, 2);
                    v___x_3046_ =
                        l_Lean_Meta_mkEqLikeNameFor(v_env_3044_, v_declName_2885_, v___x_3045_);
                    v___x_3047_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0(v_declName_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                    if leanh::lean_obj_tag(v___x_3047_) == 0 {
                        v_a_3048_ = leanh::lean_ctor_get(v___x_3047_, 0);
                        leanh::lean_inc(v_a_3048_);
                        leanh::lean_dec_ref_known(v___x_3047_, 1);
                        if leanh::lean_obj_tag(v_a_3048_) == 1 {
                            v_val_3049_ = leanh::lean_ctor_get(v_a_3048_, 0);
                            leanh::lean_inc(v_val_3049_);
                            leanh::lean_dec_ref_known(v_a_3048_, 1);
                            v___x_3050_ = lean_st_ref_get(v_a_2889_);
                            v_env_3051_ = leanh::lean_ctor_get(v___x_3050_, 0);
                            leanh::lean_inc_ref(v_env_3051_);
                            leanh::lean_dec(v___x_3050_);
                            leanh::lean_inc(v_declName_2885_);
                            v___x_3052_ = l_Lean_privateToUserName(v_declName_2885_);
                            v___x_3053_ = l_Lean_Name_str___override(v___x_3052_, v___x_3045_);
                            v___x_3054_ = l_Lean_mkPrivateNameCore(v_val_3049_, v___x_3053_);
                            leanh::lean_inc(v___x_3054_);
                            v___x_3055_ =
                                l_Lean_Environment_find_x3f(v_env_3051_, v___x_3054_, v___x_3041_);
                            if leanh::lean_obj_tag(v___x_3055_) == 1 {
                                v_val_3056_ = leanh::lean_ctor_get(v___x_3055_, 0);
                                leanh::lean_inc(v_val_3056_);
                                if leanh::lean_obj_tag(v_val_3056_) == 2 {
                                    v_isSharedCheck_3099_ =
                                        (!leanh::lean_is_exclusive(v___x_3055_)) as u8;
                                    if v_isSharedCheck_3099_ == 0 {
                                        v_unused_3100_ =
                                            leanh::lean_ctor_get(v___x_3055_, 0);
                                        leanh::lean_dec(v_unused_3100_);
                                        v___x_3058_ = v___x_3055_;
                                        v_isShared_3059_ = v_isSharedCheck_3099_;
                                        state = 24;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3055_);
                                        v___x_3058_ = leanh::lean_box(0);
                                        v_isShared_3059_ = v_isSharedCheck_3099_;
                                        state = 24;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_3056_);
                                    leanh::lean_dec(v___x_3054_);
                                    leanh::lean_dec(v___x_3046_);
                                    leanh::lean_dec(v_declName_2885_);
                                    v___x_3101_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__3(v___f_2973_, v___x_3055_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                                    leanh::lean_dec_ref_known(v___x_3055_, 1);
                                    v___y_3004_ = v___x_3042_;
                                    v___y_3005_ = v_a_3039_;
                                    v___y_3006_ = v___x_3101_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_3054_);
                                leanh::lean_dec(v___x_3046_);
                                leanh::lean_dec(v_declName_2885_);
                                v___x_3102_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__3(v___f_2973_, v___x_3055_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                                leanh::lean_dec(v___x_3055_);
                                v___y_3004_ = v___x_3042_;
                                v___y_3005_ = v_a_3039_;
                                v___y_3006_ = v___x_3102_;
                                state = 18;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3048_);
                            leanh::lean_dec(v___x_3046_);
                            leanh::lean_dec(v_declName_2885_);
                            v___x_3103_ = leanh::lean_box(0);
                            v___x_3104_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__2(v___x_3103_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                            v___y_3004_ = v___x_3042_;
                            v___y_3005_ = v_a_3039_;
                            v___y_3006_ = v___x_3104_;
                            state = 18;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3046_);
                        leanh::lean_dec(v_declName_2885_);
                        v___y_3004_ = v___x_3042_;
                        v___y_3005_ = v_a_3039_;
                        v___y_3006_ = v___x_3047_;
                        state = 18;
                        continue;
                    }
                } else {
                    v___x_3105_ = lean_io_get_num_heartbeats();
                    v___x_3106_ = lean_st_ref_get(v_a_2889_);
                    v_env_3107_ = leanh::lean_ctor_get(v___x_3106_, 0);
                    leanh::lean_inc_ref(v_env_3107_);
                    leanh::lean_dec(v___x_3106_);
                    v___x_3108_ = l_Lean_Meta_unfoldThmSuffix;
                    leanh::lean_inc_n(v_declName_2885_, 2);
                    v___x_3109_ =
                        l_Lean_Meta_mkEqLikeNameFor(v_env_3107_, v_declName_2885_, v___x_3108_);
                    v___x_3110_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0(v_declName_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                    if leanh::lean_obj_tag(v___x_3110_) == 0 {
                        v_a_3111_ = leanh::lean_ctor_get(v___x_3110_, 0);
                        leanh::lean_inc(v_a_3111_);
                        leanh::lean_dec_ref_known(v___x_3110_, 1);
                        if leanh::lean_obj_tag(v_a_3111_) == 1 {
                            v_val_3112_ = leanh::lean_ctor_get(v_a_3111_, 0);
                            leanh::lean_inc(v_val_3112_);
                            leanh::lean_dec_ref_known(v_a_3111_, 1);
                            v___x_3113_ = lean_st_ref_get(v_a_2889_);
                            v_env_3114_ = leanh::lean_ctor_get(v___x_3113_, 0);
                            leanh::lean_inc_ref(v_env_3114_);
                            leanh::lean_dec(v___x_3113_);
                            leanh::lean_inc(v_declName_2885_);
                            v___x_3115_ = l_Lean_privateToUserName(v_declName_2885_);
                            v___x_3116_ = l_Lean_Name_str___override(v___x_3115_, v___x_3108_);
                            v___x_3117_ = l_Lean_mkPrivateNameCore(v_val_3112_, v___x_3116_);
                            v___x_3118_ = 0;
                            leanh::lean_inc(v___x_3117_);
                            v___x_3119_ =
                                l_Lean_Environment_find_x3f(v_env_3114_, v___x_3117_, v___x_3118_);
                            if leanh::lean_obj_tag(v___x_3119_) == 1 {
                                v_val_3120_ = leanh::lean_ctor_get(v___x_3119_, 0);
                                leanh::lean_inc(v_val_3120_);
                                if leanh::lean_obj_tag(v_val_3120_) == 2 {
                                    v_isSharedCheck_3163_ =
                                        (!leanh::lean_is_exclusive(v___x_3119_)) as u8;
                                    if v_isSharedCheck_3163_ == 0 {
                                        v_unused_3164_ =
                                            leanh::lean_ctor_get(v___x_3119_, 0);
                                        leanh::lean_dec(v_unused_3164_);
                                        v___x_3122_ = v___x_3119_;
                                        v_isShared_3123_ = v_isSharedCheck_3163_;
                                        state = 32;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3119_);
                                        v___x_3122_ = leanh::lean_box(0);
                                        v_isShared_3123_ = v_isSharedCheck_3163_;
                                        state = 32;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_3120_);
                                    leanh::lean_dec(v___x_3117_);
                                    leanh::lean_dec(v___x_3109_);
                                    leanh::lean_dec(v_declName_2885_);
                                    v___x_3165_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__3(v___f_2973_, v___x_3119_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                                    leanh::lean_dec_ref_known(v___x_3119_, 1);
                                    v___y_3032_ = v_a_3039_;
                                    v___y_3033_ = v___x_3105_;
                                    v___y_3034_ = v___x_3165_;
                                    state = 22;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_3117_);
                                leanh::lean_dec(v___x_3109_);
                                leanh::lean_dec(v_declName_2885_);
                                v___x_3166_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__3(v___f_2973_, v___x_3119_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                                leanh::lean_dec(v___x_3119_);
                                v___y_3032_ = v_a_3039_;
                                v___y_3033_ = v___x_3105_;
                                v___y_3034_ = v___x_3166_;
                                state = 22;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3111_);
                            leanh::lean_dec(v___x_3109_);
                            leanh::lean_dec(v_declName_2885_);
                            v___x_3167_ = leanh::lean_box(0);
                            v___x_3168_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__2(v___x_3167_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
                            v___y_3032_ = v_a_3039_;
                            v___y_3033_ = v___x_3105_;
                            v___y_3034_ = v___x_3168_;
                            state = 22;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3109_);
                        leanh::lean_dec(v_declName_2885_);
                        v___y_3032_ = v_a_3039_;
                        v___y_3033_ = v___x_3105_;
                        v___y_3034_ = v___x_3110_;
                        state = 22;
                        continue;
                    }
                }
            }
            24 => {
                v_val_3060_ = leanh::lean_ctor_get(v_val_3056_, 0);
                v_isSharedCheck_3098_ = (!leanh::lean_is_exclusive(v_val_3056_)) as u8;
                if v_isSharedCheck_3098_ == 0 {
                    v___x_3062_ = v_val_3056_;
                    v_isShared_3063_ = v_isSharedCheck_3098_;
                    state = 25;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3060_);
                    leanh::lean_dec(v_val_3056_);
                    v___x_3062_ = leanh::lean_box(0);
                    v_isShared_3063_ = v_isSharedCheck_3098_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v_toConstantVal_3064_ = leanh::lean_ctor_get(v_val_3060_, 0);
                v_isSharedCheck_3095_ = (!leanh::lean_is_exclusive(v_val_3060_)) as u8;
                if v_isSharedCheck_3095_ == 0 {
                    v_unused_3096_ = leanh::lean_ctor_get(v_val_3060_, 2);
                    leanh::lean_dec(v_unused_3096_);
                    v_unused_3097_ = leanh::lean_ctor_get(v_val_3060_, 1);
                    leanh::lean_dec(v_unused_3097_);
                    v___x_3066_ = v_val_3060_;
                    v_isShared_3067_ = v_isSharedCheck_3095_;
                    state = 26;
                    continue;
                } else {
                    leanh::lean_inc(v_toConstantVal_3064_);
                    leanh::lean_dec(v_val_3060_);
                    v___x_3066_ = leanh::lean_box(0);
                    v_isShared_3067_ = v_isSharedCheck_3095_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v_levelParams_3068_ = leanh::lean_ctor_get(v_toConstantVal_3064_, 1);
                v_type_3069_ = leanh::lean_ctor_get(v_toConstantVal_3064_, 2);
                v_isSharedCheck_3093_ =
                    (!leanh::lean_is_exclusive(v_toConstantVal_3064_)) as u8;
                if v_isSharedCheck_3093_ == 0 {
                    v_unused_3094_ = leanh::lean_ctor_get(v_toConstantVal_3064_, 0);
                    leanh::lean_dec(v_unused_3094_);
                    v___x_3071_ = v_toConstantVal_3064_;
                    v_isShared_3072_ = v_isSharedCheck_3093_;
                    state = 27;
                    continue;
                } else {
                    leanh::lean_inc(v_type_3069_);
                    leanh::lean_inc(v_levelParams_3068_);
                    leanh::lean_dec(v_toConstantVal_3064_);
                    v___x_3071_ = leanh::lean_box(0);
                    v_isShared_3072_ = v_isSharedCheck_3093_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                leanh::lean_inc(v_levelParams_3068_);
                leanh::lean_inc(v___x_3046_);
                if v_isShared_3072_ == 0 {
                    leanh::lean_ctor_set(v___x_3071_, 0, v___x_3046_);
                    v___x_3074_ = v___x_3071_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3046_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_levelParams_3068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 2, v_type_3069_);
                    v___x_3074_ = v_reuseFailAlloc_3092_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_3075_ = leanh::lean_box(0);
                v___x_3076_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__1(v_levelParams_3068_, v___x_3075_);
                v___x_3077_ = l_Lean_Expr_const___override(v___x_3054_, v___x_3076_);
                leanh::lean_inc(v___x_3046_);
                v___x_3078_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3078_, 0, v___x_3046_);
                leanh::lean_ctor_set(v___x_3078_, 1, v___x_3075_);
                if v_isShared_3067_ == 0 {
                    leanh::lean_ctor_set(v___x_3066_, 2, v___x_3078_);
                    leanh::lean_ctor_set(v___x_3066_, 1, v___x_3077_);
                    leanh::lean_ctor_set(v___x_3066_, 0, v___x_3074_);
                    v___x_3080_ = v___x_3066_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3091_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 2, v___x_3078_);
                    v___x_3080_ = v_reuseFailAlloc_3091_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_3063_ == 0 {
                    leanh::lean_ctor_set(v___x_3062_, 0, v___x_3080_);
                    v___x_3082_ = v___x_3062_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3080_);
                    v___x_3082_ = v_reuseFailAlloc_3090_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3083_ = leanh::lean_box((v___x_3041_) as usize);
                v___f_3084_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__6___boxed as *mut core::ffi::c_void, 7, 2);
                leanh::lean_closure_set(v___f_3084_, 0, v___x_3082_);
                leanh::lean_closure_set(v___f_3084_, 1, v___x_3083_);
                leanh::lean_inc(v___x_3046_);
                v___x_3085_ = l_Lean_Meta_realizeConst(
                    v_declName_2885_,
                    v___x_3046_,
                    v___f_3084_,
                    v_a_2886_,
                    v_a_2887_,
                    v_a_2888_,
                    v_a_2889_,
                );
                if leanh::lean_obj_tag(v___x_3085_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3085_, 1);
                    if v_isShared_3059_ == 0 {
                        leanh::lean_ctor_set(v___x_3058_, 0, v___x_3046_);
                        v___x_3087_ = v___x_3058_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3046_);
                        v___x_3087_ = v_reuseFailAlloc_3088_;
                        state = 31;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3058_);
                    leanh::lean_dec(v___x_3046_);
                    v_a_3089_ = leanh::lean_ctor_get(v___x_3085_, 0);
                    leanh::lean_inc(v_a_3089_);
                    leanh::lean_dec_ref_known(v___x_3085_, 1);
                    v___y_2994_ = v___x_3042_;
                    v___y_2995_ = v_a_3039_;
                    v_a_2996_ = v_a_3089_;
                    state = 16;
                    continue;
                }
            }
            31 => {
                v___y_2999_ = v___x_3042_;
                v___y_3000_ = v_a_3039_;
                v_a_3001_ = v___x_3087_;
                state = 17;
                continue;
            }
            32 => {
                v_val_3124_ = leanh::lean_ctor_get(v_val_3120_, 0);
                v_isSharedCheck_3162_ = (!leanh::lean_is_exclusive(v_val_3120_)) as u8;
                if v_isSharedCheck_3162_ == 0 {
                    v___x_3126_ = v_val_3120_;
                    v_isShared_3127_ = v_isSharedCheck_3162_;
                    state = 33;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3124_);
                    leanh::lean_dec(v_val_3120_);
                    v___x_3126_ = leanh::lean_box(0);
                    v_isShared_3127_ = v_isSharedCheck_3162_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v_toConstantVal_3128_ = leanh::lean_ctor_get(v_val_3124_, 0);
                v_isSharedCheck_3159_ = (!leanh::lean_is_exclusive(v_val_3124_)) as u8;
                if v_isSharedCheck_3159_ == 0 {
                    v_unused_3160_ = leanh::lean_ctor_get(v_val_3124_, 2);
                    leanh::lean_dec(v_unused_3160_);
                    v_unused_3161_ = leanh::lean_ctor_get(v_val_3124_, 1);
                    leanh::lean_dec(v_unused_3161_);
                    v___x_3130_ = v_val_3124_;
                    v_isShared_3131_ = v_isSharedCheck_3159_;
                    state = 34;
                    continue;
                } else {
                    leanh::lean_inc(v_toConstantVal_3128_);
                    leanh::lean_dec(v_val_3124_);
                    v___x_3130_ = leanh::lean_box(0);
                    v_isShared_3131_ = v_isSharedCheck_3159_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v_levelParams_3132_ = leanh::lean_ctor_get(v_toConstantVal_3128_, 1);
                v_type_3133_ = leanh::lean_ctor_get(v_toConstantVal_3128_, 2);
                v_isSharedCheck_3157_ =
                    (!leanh::lean_is_exclusive(v_toConstantVal_3128_)) as u8;
                if v_isSharedCheck_3157_ == 0 {
                    v_unused_3158_ = leanh::lean_ctor_get(v_toConstantVal_3128_, 0);
                    leanh::lean_dec(v_unused_3158_);
                    v___x_3135_ = v_toConstantVal_3128_;
                    v_isShared_3136_ = v_isSharedCheck_3157_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_type_3133_);
                    leanh::lean_inc(v_levelParams_3132_);
                    leanh::lean_dec(v_toConstantVal_3128_);
                    v___x_3135_ = leanh::lean_box(0);
                    v_isShared_3136_ = v_isSharedCheck_3157_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                leanh::lean_inc(v_levelParams_3132_);
                leanh::lean_inc(v___x_3109_);
                if v_isShared_3136_ == 0 {
                    leanh::lean_ctor_set(v___x_3135_, 0, v___x_3109_);
                    v___x_3138_ = v___x_3135_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3156_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_levelParams_3132_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_type_3133_);
                    v___x_3138_ = v_reuseFailAlloc_3156_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_3139_ = leanh::lean_box(0);
                v___x_3140_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__1(v_levelParams_3132_, v___x_3139_);
                v___x_3141_ = l_Lean_Expr_const___override(v___x_3117_, v___x_3140_);
                leanh::lean_inc(v___x_3109_);
                v___x_3142_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3142_, 0, v___x_3109_);
                leanh::lean_ctor_set(v___x_3142_, 1, v___x_3139_);
                if v_isShared_3131_ == 0 {
                    leanh::lean_ctor_set(v___x_3130_, 2, v___x_3142_);
                    leanh::lean_ctor_set(v___x_3130_, 1, v___x_3141_);
                    leanh::lean_ctor_set(v___x_3130_, 0, v___x_3138_);
                    v___x_3144_ = v___x_3130_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 1, v___x_3141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 2, v___x_3142_);
                    v___x_3144_ = v_reuseFailAlloc_3155_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3127_ == 0 {
                    leanh::lean_ctor_set(v___x_3126_, 0, v___x_3144_);
                    v___x_3146_ = v___x_3126_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3144_);
                    v___x_3146_ = v_reuseFailAlloc_3154_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_3147_ = leanh::lean_box((v___x_3118_) as usize);
                v___f_3148_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__6___boxed as *mut core::ffi::c_void, 7, 2);
                leanh::lean_closure_set(v___f_3148_, 0, v___x_3146_);
                leanh::lean_closure_set(v___f_3148_, 1, v___x_3147_);
                leanh::lean_inc(v___x_3109_);
                v___x_3149_ = l_Lean_Meta_realizeConst(
                    v_declName_2885_,
                    v___x_3109_,
                    v___f_3148_,
                    v_a_2886_,
                    v_a_2887_,
                    v_a_2888_,
                    v_a_2889_,
                );
                if leanh::lean_obj_tag(v___x_3149_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3149_, 1);
                    if v_isShared_3123_ == 0 {
                        leanh::lean_ctor_set(v___x_3122_, 0, v___x_3109_);
                        v___x_3151_ = v___x_3122_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_3152_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3109_);
                        v___x_3151_ = v_reuseFailAlloc_3152_;
                        state = 39;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3122_);
                    leanh::lean_dec(v___x_3109_);
                    v_a_3153_ = leanh::lean_ctor_get(v___x_3149_, 0);
                    leanh::lean_inc(v_a_3153_);
                    leanh::lean_dec_ref_known(v___x_3149_, 1);
                    v___y_3027_ = v_a_3039_;
                    v___y_3028_ = v___x_3105_;
                    v_a_3029_ = v_a_3153_;
                    state = 21;
                    continue;
                }
            }
            39 => {
                v___y_3022_ = v_a_3039_;
                v___y_3023_ = v___x_3105_;
                v_a_3024_ = v___x_3151_;
                state = 20;
                continue;
            }
            40 => {
                if leanh::lean_obj_tag(v_val_3184_) == 2 {
                    v_val_3188_ = leanh::lean_ctor_get(v_val_3184_, 0);
                    v_isSharedCheck_3241_ = (!leanh::lean_is_exclusive(v_val_3184_)) as u8;
                    if v_isSharedCheck_3241_ == 0 {
                        v___x_3190_ = v_val_3184_;
                        v_isShared_3191_ = v_isSharedCheck_3241_;
                        state = 41;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3188_);
                        leanh::lean_dec(v_val_3184_);
                        v___x_3190_ = leanh::lean_box(0);
                        v_isShared_3191_ = v_isSharedCheck_3241_;
                        state = 41;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3186_);
                    leanh::lean_dec(v_val_3184_);
                    leanh::lean_dec(v___x_3182_);
                    leanh::lean_dec(v___x_3174_);
                    leanh::lean_dec(v_declName_2885_);
                    state = 1;
                    continue;
                }
            }
            41 => {
                v_toConstantVal_3192_ = leanh::lean_ctor_get(v_val_3188_, 0);
                v_isSharedCheck_3238_ = (!leanh::lean_is_exclusive(v_val_3188_)) as u8;
                if v_isSharedCheck_3238_ == 0 {
                    v_unused_3239_ = leanh::lean_ctor_get(v_val_3188_, 2);
                    leanh::lean_dec(v_unused_3239_);
                    v_unused_3240_ = leanh::lean_ctor_get(v_val_3188_, 1);
                    leanh::lean_dec(v_unused_3240_);
                    v___x_3194_ = v_val_3188_;
                    v_isShared_3195_ = v_isSharedCheck_3238_;
                    state = 42;
                    continue;
                } else {
                    leanh::lean_inc(v_toConstantVal_3192_);
                    leanh::lean_dec(v_val_3188_);
                    v___x_3194_ = leanh::lean_box(0);
                    v_isShared_3195_ = v_isSharedCheck_3238_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v_levelParams_3196_ = leanh::lean_ctor_get(v_toConstantVal_3192_, 1);
                v_type_3197_ = leanh::lean_ctor_get(v_toConstantVal_3192_, 2);
                v_isSharedCheck_3236_ =
                    (!leanh::lean_is_exclusive(v_toConstantVal_3192_)) as u8;
                if v_isSharedCheck_3236_ == 0 {
                    v_unused_3237_ = leanh::lean_ctor_get(v_toConstantVal_3192_, 0);
                    leanh::lean_dec(v_unused_3237_);
                    v___x_3199_ = v_toConstantVal_3192_;
                    v_isShared_3200_ = v_isSharedCheck_3236_;
                    state = 43;
                    continue;
                } else {
                    leanh::lean_inc(v_type_3197_);
                    leanh::lean_inc(v_levelParams_3196_);
                    leanh::lean_dec(v_toConstantVal_3192_);
                    v___x_3199_ = leanh::lean_box(0);
                    v_isShared_3200_ = v_isSharedCheck_3236_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                leanh::lean_inc(v_levelParams_3196_);
                leanh::lean_inc(v___x_3174_);
                if v_isShared_3200_ == 0 {
                    leanh::lean_ctor_set(v___x_3199_, 0, v___x_3174_);
                    v___x_3202_ = v___x_3199_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3235_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3174_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_levelParams_3196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_type_3197_);
                    v___x_3202_ = v_reuseFailAlloc_3235_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3203_ = leanh::lean_box(0);
                v___x_3204_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__1(v_levelParams_3196_, v___x_3203_);
                v___x_3205_ = l_Lean_Expr_const___override(v___x_3182_, v___x_3204_);
                leanh::lean_inc(v___x_3174_);
                v___x_3206_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3206_, 0, v___x_3174_);
                leanh::lean_ctor_set(v___x_3206_, 1, v___x_3203_);
                if v_isShared_3195_ == 0 {
                    leanh::lean_ctor_set(v___x_3194_, 2, v___x_3206_);
                    leanh::lean_ctor_set(v___x_3194_, 1, v___x_3205_);
                    leanh::lean_ctor_set(v___x_3194_, 0, v___x_3202_);
                    v___x_3208_ = v___x_3194_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3234_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3234_, 2, v___x_3206_);
                    v___x_3208_ = v_reuseFailAlloc_3234_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3191_ == 0 {
                    leanh::lean_ctor_set(v___x_3190_, 0, v___x_3208_);
                    v___x_3210_ = v___x_3190_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3233_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3208_);
                    v___x_3210_ = v_reuseFailAlloc_3233_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                v___x_3211_ = leanh::lean_box((v___x_3170_) as usize);
                v___f_3212_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___lam__6___boxed as *mut core::ffi::c_void, 7, 2);
                leanh::lean_closure_set(v___f_3212_, 0, v___x_3210_);
                leanh::lean_closure_set(v___f_3212_, 1, v___x_3211_);
                leanh::lean_inc(v___x_3174_);
                v___x_3213_ = l_Lean_Meta_realizeConst(
                    v_declName_2885_,
                    v___x_3174_,
                    v___f_3212_,
                    v_a_2886_,
                    v_a_2887_,
                    v_a_2888_,
                    v_a_2889_,
                );
                if leanh::lean_obj_tag(v___x_3213_) == 0 {
                    v_isSharedCheck_3223_ = (!leanh::lean_is_exclusive(v___x_3213_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v_unused_3224_ = leanh::lean_ctor_get(v___x_3213_, 0);
                        leanh::lean_dec(v_unused_3224_);
                        v___x_3215_ = v___x_3213_;
                        v_isShared_3216_ = v_isSharedCheck_3223_;
                        state = 47;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3213_);
                        v___x_3215_ = leanh::lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3223_;
                        state = 47;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3186_);
                    leanh::lean_dec(v___x_3174_);
                    v_a_3225_ = leanh::lean_ctor_get(v___x_3213_, 0);
                    v_isSharedCheck_3232_ = (!leanh::lean_is_exclusive(v___x_3213_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3227_ = v___x_3213_;
                        v_isShared_3228_ = v_isSharedCheck_3232_;
                        state = 50;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3225_);
                        leanh::lean_dec(v___x_3213_);
                        v___x_3227_ = leanh::lean_box(0);
                        v_isShared_3228_ = v_isSharedCheck_3232_;
                        state = 50;
                        continue;
                    }
                }
            }
            47 => {
                if v_isShared_3187_ == 0 {
                    leanh::lean_ctor_set(v___x_3186_, 0, v___x_3174_);
                    v___x_3218_ = v___x_3186_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3174_);
                    v___x_3218_ = v_reuseFailAlloc_3222_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                if v_isShared_3216_ == 0 {
                    leanh::lean_ctor_set(v___x_3215_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3215_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_3220_;
            }
            50 => {
                if v_isShared_3228_ == 0 {
                    v___x_3230_ = v___x_3227_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_3230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___boxed(
    mut v_declName_3243_: *mut leanh::LeanObject,
    mut v_a_3244_: *mut leanh::LeanObject,
    mut v_a_3245_: *mut leanh::LeanObject,
    mut v_a_3246_: *mut leanh::LeanObject,
    mut v_a_3247_: *mut leanh::LeanObject,
    mut v_a_3248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3249_ =
        l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem(
            v_declName_3243_,
            v_a_3244_,
            v_a_3245_,
            v_a_3246_,
            v_a_3247_,
        );
    leanh::lean_dec(v_a_3247_);
    leanh::lean_dec_ref(v_a_3246_);
    leanh::lean_dec(v_a_3245_);
    leanh::lean_dec_ref(v_a_3244_);
    return v_res_3249_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7(
    mut v_00_u03b1_3250_: *mut leanh::LeanObject,
    mut v_x_3251_: *mut leanh::LeanObject,
    mut v___y_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3257_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7___redArg(v_x_3251_);
    return v___x_3257_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7___boxed(
    mut v_00_u03b1_3258_: *mut leanh::LeanObject,
    mut v_x_3259_: *mut leanh::LeanObject,
    mut v___y_3260_: *mut leanh::LeanObject,
    mut v___y_3261_: *mut leanh::LeanObject,
    mut v___y_3262_: *mut leanh::LeanObject,
    mut v___y_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3265_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__4_spec__7(v_00_u03b1_3258_, v_x_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
    leanh::lean_dec(v___y_3263_);
    leanh::lean_dec_ref(v___y_3262_);
    leanh::lean_dec(v___y_3261_);
    leanh::lean_dec_ref(v___y_3260_);
    return v_res_3265_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3(
    mut v_00_u03b1_3266_: *mut leanh::LeanObject,
    mut v_constName_3267_: *mut leanh::LeanObject,
    mut v___y_3268_: *mut leanh::LeanObject,
    mut v___y_3269_: *mut leanh::LeanObject,
    mut v___y_3270_: *mut leanh::LeanObject,
    mut v___y_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3273_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3___redArg(v_constName_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
    return v___x_3273_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_3274_: *mut leanh::LeanObject,
    mut v_constName_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
    mut v___y_3277_: *mut leanh::LeanObject,
    mut v___y_3278_: *mut leanh::LeanObject,
    mut v___y_3279_: *mut leanh::LeanObject,
    mut v___y_3280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3281_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3(v_00_u03b1_3274_, v_constName_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
    leanh::lean_dec(v___y_3279_);
    leanh::lean_dec_ref(v___y_3278_);
    leanh::lean_dec(v___y_3277_);
    leanh::lean_dec_ref(v___y_3276_);
    return v_res_3281_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9(
    mut v_00_u03b1_3282_: *mut leanh::LeanObject,
    mut v_ref_3283_: *mut leanh::LeanObject,
    mut v_constName_3284_: *mut leanh::LeanObject,
    mut v___y_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
    mut v___y_3287_: *mut leanh::LeanObject,
    mut v___y_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_ref_3283_, v_constName_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
    return v___x_3290_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9___boxed(
    mut v_00_u03b1_3291_: *mut leanh::LeanObject,
    mut v_ref_3292_: *mut leanh::LeanObject,
    mut v_constName_3293_: *mut leanh::LeanObject,
    mut v___y_3294_: *mut leanh::LeanObject,
    mut v___y_3295_: *mut leanh::LeanObject,
    mut v___y_3296_: *mut leanh::LeanObject,
    mut v___y_3297_: *mut leanh::LeanObject,
    mut v___y_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3299_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9(v_00_u03b1_3291_, v_ref_3292_, v_constName_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
    leanh::lean_dec(v___y_3297_);
    leanh::lean_dec_ref(v___y_3296_);
    leanh::lean_dec(v___y_3295_);
    leanh::lean_dec_ref(v___y_3294_);
    leanh::lean_dec(v_ref_3292_);
    return v_res_3299_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12(
    mut v_00_u03b1_3300_: *mut leanh::LeanObject,
    mut v_ref_3301_: *mut leanh::LeanObject,
    mut v_msg_3302_: *mut leanh::LeanObject,
    mut v_declHint_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
    mut v___y_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3309_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12___redArg(v_ref_3301_, v_msg_3302_, v_declHint_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
    return v___x_3309_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12___boxed(
    mut v_00_u03b1_3310_: *mut leanh::LeanObject,
    mut v_ref_3311_: *mut leanh::LeanObject,
    mut v_msg_3312_: *mut leanh::LeanObject,
    mut v_declHint_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
    mut v___y_3315_: *mut leanh::LeanObject,
    mut v___y_3316_: *mut leanh::LeanObject,
    mut v___y_3317_: *mut leanh::LeanObject,
    mut v___y_3318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12(v_00_u03b1_3310_, v_ref_3311_, v_msg_3312_, v_declHint_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
    leanh::lean_dec(v___y_3317_);
    leanh::lean_dec_ref(v___y_3316_);
    leanh::lean_dec(v___y_3315_);
    leanh::lean_dec_ref(v___y_3314_);
    leanh::lean_dec(v_ref_3311_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15(
    mut v_msg_3320_: *mut leanh::LeanObject,
    mut v_declHint_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
    mut v___y_3323_: *mut leanh::LeanObject,
    mut v___y_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___redArg(v_msg_3320_, v_declHint_3321_, v___y_3325_);
    return v___x_3327_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15___boxed(
    mut v_msg_3328_: *mut leanh::LeanObject,
    mut v_declHint_3329_: *mut leanh::LeanObject,
    mut v___y_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3335_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__14_spec__15(v_msg_3328_, v_declHint_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
    leanh::lean_dec(v___y_3333_);
    leanh::lean_dec_ref(v___y_3332_);
    leanh::lean_dec(v___y_3331_);
    leanh::lean_dec_ref(v___y_3330_);
    return v_res_3335_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15(
    mut v_00_u03b1_3336_: *mut leanh::LeanObject,
    mut v_ref_3337_: *mut leanh::LeanObject,
    mut v_msg_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15___redArg(v_ref_3337_, v_msg_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
    return v___x_3344_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15___boxed(
    mut v_00_u03b1_3345_: *mut leanh::LeanObject,
    mut v_ref_3346_: *mut leanh::LeanObject,
    mut v_msg_3347_: *mut leanh::LeanObject,
    mut v___y_3348_: *mut leanh::LeanObject,
    mut v___y_3349_: *mut leanh::LeanObject,
    mut v___y_3350_: *mut leanh::LeanObject,
    mut v___y_3351_: *mut leanh::LeanObject,
    mut v___y_3352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15(v_00_u03b1_3345_, v_ref_3346_, v_msg_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
    leanh::lean_dec(v___y_3351_);
    leanh::lean_dec_ref(v___y_3350_);
    leanh::lean_dec(v___y_3349_);
    leanh::lean_dec_ref(v___y_3348_);
    leanh::lean_dec(v_ref_3346_);
    return v_res_3353_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17(
    mut v_00_u03b1_3354_: *mut leanh::LeanObject,
    mut v_msg_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3361_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17___redArg(v_msg_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
    return v___x_3361_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17___boxed(
    mut v_00_u03b1_3362_: *mut leanh::LeanObject,
    mut v_msg_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
    mut v___y_3366_: *mut leanh::LeanObject,
    mut v___y_3367_: *mut leanh::LeanObject,
    mut v___y_3368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3369_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem_spec__0_spec__0_spec__3_spec__9_spec__12_spec__15_spec__17(v_00_u03b1_3362_, v_msg_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
    leanh::lean_dec(v___y_3367_);
    leanh::lean_dec_ref(v___y_3366_);
    leanh::lean_dec(v___y_3365_);
    leanh::lean_dec_ref(v___y_3364_);
    return v_res_3369_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_2013126914____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3371_ = leanh::lean_alloc_closure(
        l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_copyPrivateUnfoldTheorem___boxed
            as *mut core::ffi::c_void,
        6,
        0,
    );
    v___x_3372_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3371_);
    return v___x_3372_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_2013126914____hygCtx___hyg_2____boxed(
    mut v_a_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3374_ = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_2013126914____hygCtx___hyg_2_();
    return v_res_3374_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ArgsPacker_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_WF_instInhabitedEqnInfo_default =
        _init_l_Lean_Elab_WF_instInhabitedEqnInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_WF_instInhabitedEqnInfo_default);
    l_Lean_Elab_WF_instInhabitedEqnInfo = _init_l_Lean_Elab_WF_instInhabitedEqnInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_WF_instInhabitedEqnInfo);
    res = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_1195399529____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_WF_eqnInfoExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_WF_eqnInfoExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_WF_Eqns_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Eqns_2013126914____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_WF_Eqns(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_WF_Eqns(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_ArgsPacker_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
}