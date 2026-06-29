// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrites
// Imports: Lean.Elab.Tactic.Location Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Rewrites
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::GetElem::l_List_get_x3fInternal___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_mkOptionalNode};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_empty, l_Lean_NameSet_insert};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_evalTactic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    l_Lean_Elab_Tactic_withLocation, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_fvar___override, l_Lean_Expr_hasMVar, l_Lean_mkFVar};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_isImplementationDetail;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEqMP;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_FVarId_findDecl_x3f___redArg, l_Lean_FVarId_getType___redArg,
    l_Lean_FVarId_getUserName___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_replace, l_Lean_MVarId_replaceTargetEq,
    runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Rewrites::{
    initialize_Lean_Meta_Tactic_Rewrites, l_Lean_Meta_Rewrites_RewriteResult_addSuggestion,
    l_Lean_Meta_Rewrites_createModuleTreeRef, l_Lean_Meta_Rewrites_findRewrites,
    l_Lean_Meta_Rewrites_localHypotheses, runtime_initialize_Lean_Meta_Tactic_Rewrites,
};
use crate::r#gen::Lean::Meta::Tactic::TryThis::l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Heartbeats::l_Lean_reportOutOfHeartbeats;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 97, 32, 114, 101,
        119, 114, 105, 116, 101, 32, 102, 111, 114, 32, 115, 111, 109, 101, 32, 108, 111, 99, 97,
        116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [114, 101, 119, 114, 105, 116, 101, 115, 0],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1029260601596685885 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2_value:
    crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 97, 110, 121, 32,
        108, 101, 109, 109, 97, 115, 32, 119, 104, 105, 99, 104, 32, 99, 97, 110, 32, 114, 101,
        119, 114, 105, 116, 101, 32, 116, 104, 101, 32, 104, 121, 112, 111, 116, 104, 101, 115,
        105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 114, 121, 0],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 102, 108, 0],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8_value:
    crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 97, 110, 121, 32,
        108, 101, 109, 109, 97, 115, 32, 119, 104, 105, 99, 104, 32, 99, 97, 110, 32, 114, 101,
        119, 114, 105, 116, 101, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0,
    ],
};
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0_value) as *mut crate::leanh::LeanObject,2214559063752339918 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Rewrites_evalExact___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Rewrites_evalExact___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [114, 101, 119, 114, 105, 116, 101, 115, 63, 0],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Rewrites_evalExact___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__3_value)
                as *mut crate::leanh::LeanObject,
            5113271700673181263 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Rewrites_evalExact___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__6_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [102, 105, 110, 100, 82, 101, 119, 114, 105, 116, 101, 115, 0],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__6_value)
                as *mut crate::leanh::LeanObject,
            16853624364780600316 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__8_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__9_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            114, 101, 119, 114, 105, 116, 101, 115, 95, 102, 111, 114, 98, 105, 100, 100, 101, 110,
            0,
        ],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Rewrites_evalExact___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__9_value)
                as *mut crate::leanh::LeanObject,
            2332491506864073911 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Rewrites_evalExact___closed__11_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Rewrites_evalExact___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [82, 101, 119, 114, 105, 116, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 69, 120, 97, 99, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Rewrites_evalExact___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1_value) as *mut crate::leanh::LeanObject,5274862542269108301 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2_value) as *mut crate::leanh::LeanObject,6715241009838729468 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 67 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 70 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 70 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ = crate::leanh::lean_box(0);
    v___x_1219_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1220_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
    crate::leanh::lean_ctor_set(v___x_1220_, 1, v___x_1218_);
    return v___x_1220_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0);
    v___x_1223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
    return v___x_1223_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(
    mut v___y_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
    return v_res_1225_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(
    mut v_00_u03b1_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
    return v___x_1236_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(
    mut v_00_u03b1_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1247_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(
        v_00_u03b1_1237_,
        v___y_1238_,
        v___y_1239_,
        v___y_1240_,
        v___y_1241_,
        v___y_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
    );
    crate::leanh::lean_dec(v___y_1245_);
    crate::leanh::lean_dec_ref(v___y_1244_);
    crate::leanh::lean_dec(v___y_1243_);
    crate::leanh::lean_dec_ref(v___y_1242_);
    crate::leanh::lean_dec(v___y_1241_);
    crate::leanh::lean_dec_ref(v___y_1240_);
    crate::leanh::lean_dec(v___y_1239_);
    crate::leanh::lean_dec_ref(v___y_1238_);
    return v_res_1247_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(
    mut v_e_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_unused_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1251_ = l_Lean_Expr_hasMVar(v_e_1248_);
                if v___x_1251_ == 0 {
                    v___x_1252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1252_, 0, v_e_1248_);
                    return v___x_1252_;
                } else {
                    v___x_1253_ = lean_st_ref_get(v___y_1249_);
                    v_mctx_1254_ = crate::leanh::lean_ctor_get(v___x_1253_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1254_);
                    crate::leanh::lean_dec(v___x_1253_);
                    v___x_1255_ = l_Lean_instantiateMVarsCore(v_mctx_1254_, v_e_1248_);
                    v_fst_1256_ = crate::leanh::lean_ctor_get(v___x_1255_, 0);
                    crate::leanh::lean_inc(v_fst_1256_);
                    v_snd_1257_ = crate::leanh::lean_ctor_get(v___x_1255_, 1);
                    crate::leanh::lean_inc(v_snd_1257_);
                    crate::leanh::lean_dec_ref(v___x_1255_);
                    v___x_1258_ = lean_st_ref_take(v___y_1249_);
                    v_cache_1259_ = crate::leanh::lean_ctor_get(v___x_1258_, 1);
                    v_zetaDeltaFVarIds_1260_ = crate::leanh::lean_ctor_get(v___x_1258_, 2);
                    v_postponed_1261_ = crate::leanh::lean_ctor_get(v___x_1258_, 3);
                    v_diag_1262_ = crate::leanh::lean_ctor_get(v___x_1258_, 4);
                    v_isSharedCheck_1271_ = (!crate::leanh::lean_is_exclusive(v___x_1258_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v_unused_1272_ = crate::leanh::lean_ctor_get(v___x_1258_, 0);
                        crate::leanh::lean_dec(v_unused_1272_);
                        v___x_1264_ = v___x_1258_;
                        v_isShared_1265_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1262_);
                        crate::leanh::lean_inc(v_postponed_1261_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1260_);
                        crate::leanh::lean_inc(v_cache_1259_);
                        crate::leanh::lean_dec(v___x_1258_);
                        v___x_1264_ = crate::leanh::lean_box(0);
                        v_isShared_1265_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1264_, 0, v_snd_1257_);
                    v___x_1267_ = v___x_1264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_snd_1257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_cache_1259_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1270_,
                        2,
                        v_zetaDeltaFVarIds_1260_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_postponed_1261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_diag_1262_);
                    v___x_1267_ = v_reuseFailAlloc_1270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1268_ = lean_st_ref_set(v___y_1249_, v___x_1267_);
                v___x_1269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1269_, 0, v_fst_1256_);
                return v___x_1269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg___boxed(
    mut v_e_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(
        v_e_1273_,
        v___y_1274_,
    );
    crate::leanh::lean_dec(v___y_1274_);
    return v_res_1276_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(
    mut v_e_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
    mut v___y_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
    mut v___y_1284_: *mut crate::leanh::LeanObject,
    mut v___y_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(
        v_e_1277_,
        v___y_1283_,
    );
    return v___x_1287_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___boxed(
    mut v_e_1288_: *mut crate::leanh::LeanObject,
    mut v___y_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(
        v_e_1288_,
        v___y_1289_,
        v___y_1290_,
        v___y_1291_,
        v___y_1292_,
        v___y_1293_,
        v___y_1294_,
        v___y_1295_,
        v___y_1296_,
    );
    crate::leanh::lean_dec(v___y_1296_);
    crate::leanh::lean_dec_ref(v___y_1295_);
    crate::leanh::lean_dec(v___y_1294_);
    crate::leanh::lean_dec_ref(v___y_1293_);
    crate::leanh::lean_dec(v___y_1292_);
    crate::leanh::lean_dec_ref(v___y_1291_);
    crate::leanh::lean_dec(v___y_1290_);
    crate::leanh::lean_dec_ref(v___y_1289_);
    return v_res_1298_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(
    mut v_x_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1303_);
    crate::leanh::lean_inc_ref(v___y_1302_);
    crate::leanh::lean_inc(v___y_1301_);
    crate::leanh::lean_inc_ref(v___y_1300_);
    v___x_1309_ = crate::leanh::lean_apply_9(
        v_x_1299_,
        v___y_1300_,
        v___y_1301_,
        v___y_1302_,
        v___y_1303_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
        crate::leanh::lean_box(0),
    );
    return v___x_1309_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed(
    mut v_x_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ =
        l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(
            v_x_1310_,
            v___y_1311_,
            v___y_1312_,
            v___y_1313_,
            v___y_1314_,
            v___y_1315_,
            v___y_1316_,
            v___y_1317_,
            v___y_1318_,
        );
    crate::leanh::lean_dec(v___y_1314_);
    crate::leanh::lean_dec_ref(v___y_1313_);
    crate::leanh::lean_dec(v___y_1312_);
    crate::leanh::lean_dec_ref(v___y_1311_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(
    mut v_mctx_1321_: *mut crate::leanh::LeanObject,
    mut v_x_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1326_);
                crate::leanh::lean_inc_ref(v___y_1325_);
                crate::leanh::lean_inc(v___y_1324_);
                crate::leanh::lean_inc_ref(v___y_1323_);
                v___f_1332_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_1332_, 0, v_x_1322_);
                crate::leanh::lean_closure_set(v___f_1332_, 1, v___y_1323_);
                crate::leanh::lean_closure_set(v___f_1332_, 2, v___y_1324_);
                crate::leanh::lean_closure_set(v___f_1332_, 3, v___y_1325_);
                crate::leanh::lean_closure_set(v___f_1332_, 4, v___y_1326_);
                v___x_1333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(
                    crate::leanh::lean_box(0),
                    v_mctx_1321_,
                    v___f_1332_,
                    v___y_1327_,
                    v___y_1328_,
                    v___y_1329_,
                    v___y_1330_,
                );
                if crate::leanh::lean_obj_tag(v___x_1333_) == 0 {
                    return v___x_1333_;
                } else {
                    v_a_1334_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                    v_isSharedCheck_1341_ = (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                    if v_isSharedCheck_1341_ == 0 {
                        v___x_1336_ = v___x_1333_;
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1334_);
                        crate::leanh::lean_dec(v___x_1333_);
                        v___x_1336_ = crate::leanh::lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1337_ == 0 {
                    v___x_1339_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
                    v___x_1339_ = v_reuseFailAlloc_1340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___boxed(
    mut v_mctx_1342_: *mut crate::leanh::LeanObject,
    mut v_x_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1353_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(
        v_mctx_1342_,
        v_x_1343_,
        v___y_1344_,
        v___y_1345_,
        v___y_1346_,
        v___y_1347_,
        v___y_1348_,
        v___y_1349_,
        v___y_1350_,
        v___y_1351_,
    );
    crate::leanh::lean_dec(v___y_1351_);
    crate::leanh::lean_dec_ref(v___y_1350_);
    crate::leanh::lean_dec(v___y_1349_);
    crate::leanh::lean_dec_ref(v___y_1348_);
    crate::leanh::lean_dec(v___y_1347_);
    crate::leanh::lean_dec_ref(v___y_1346_);
    crate::leanh::lean_dec(v___y_1345_);
    crate::leanh::lean_dec_ref(v___y_1344_);
    return v_res_1353_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(
    mut v_00_u03b1_1354_: *mut crate::leanh::LeanObject,
    mut v_mctx_1355_: *mut crate::leanh::LeanObject,
    mut v_x_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(
        v_mctx_1355_,
        v_x_1356_,
        v___y_1357_,
        v___y_1358_,
        v___y_1359_,
        v___y_1360_,
        v___y_1361_,
        v___y_1362_,
        v___y_1363_,
        v___y_1364_,
    );
    return v___x_1366_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___boxed(
    mut v_00_u03b1_1367_: *mut crate::leanh::LeanObject,
    mut v_mctx_1368_: *mut crate::leanh::LeanObject,
    mut v_x_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(
        v_00_u03b1_1367_,
        v_mctx_1368_,
        v_x_1369_,
        v___y_1370_,
        v___y_1371_,
        v___y_1372_,
        v___y_1373_,
        v___y_1374_,
        v___y_1375_,
        v___y_1376_,
        v___y_1377_,
    );
    crate::leanh::lean_dec(v___y_1377_);
    crate::leanh::lean_dec_ref(v___y_1376_);
    crate::leanh::lean_dec(v___y_1375_);
    crate::leanh::lean_dec_ref(v___y_1374_);
    crate::leanh::lean_dec(v___y_1373_);
    crate::leanh::lean_dec_ref(v___y_1372_);
    crate::leanh::lean_dec(v___y_1371_);
    crate::leanh::lean_dec_ref(v___y_1370_);
    return v_res_1379_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(
    mut v_mvarId_1380_: *mut crate::leanh::LeanObject,
    mut v_x_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_a_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1399_: u8 = 0;
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1387_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1380_,
                    v_x_1381_,
                    v___y_1382_,
                    v___y_1383_,
                    v___y_1384_,
                    v___y_1385_,
                );
                if crate::leanh::lean_obj_tag(v___x_1387_) == 0 {
                    v_a_1388_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                    v_isSharedCheck_1395_ = (!crate::leanh::lean_is_exclusive(v___x_1387_)) as u8;
                    if v_isSharedCheck_1395_ == 0 {
                        v___x_1390_ = v___x_1387_;
                        v_isShared_1391_ = v_isSharedCheck_1395_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1388_);
                        crate::leanh::lean_dec(v___x_1387_);
                        v___x_1390_ = crate::leanh::lean_box(0);
                        v_isShared_1391_ = v_isSharedCheck_1395_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1396_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                    v_isSharedCheck_1403_ = (!crate::leanh::lean_is_exclusive(v___x_1387_)) as u8;
                    if v_isSharedCheck_1403_ == 0 {
                        v___x_1398_ = v___x_1387_;
                        v_isShared_1399_ = v_isSharedCheck_1403_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1396_);
                        crate::leanh::lean_dec(v___x_1387_);
                        v___x_1398_ = crate::leanh::lean_box(0);
                        v_isShared_1399_ = v_isSharedCheck_1403_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1391_ == 0 {
                    v___x_1393_ = v___x_1390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
                    v___x_1393_ = v_reuseFailAlloc_1394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1393_;
            }
            3 => {
                if v_isShared_1399_ == 0 {
                    v___x_1401_ = v___x_1398_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1402_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
                    v___x_1401_ = v_reuseFailAlloc_1402_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg___boxed(
    mut v_mvarId_1404_: *mut crate::leanh::LeanObject,
    mut v_x_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(
        v_mvarId_1404_,
        v_x_1405_,
        v___y_1406_,
        v___y_1407_,
        v___y_1408_,
        v___y_1409_,
    );
    crate::leanh::lean_dec(v___y_1409_);
    crate::leanh::lean_dec_ref(v___y_1408_);
    crate::leanh::lean_dec(v___y_1407_);
    crate::leanh::lean_dec_ref(v___y_1406_);
    return v_res_1411_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(
    mut v_00_u03b1_1412_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1413_: *mut crate::leanh::LeanObject,
    mut v_x_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(
        v_mvarId_1413_,
        v_x_1414_,
        v___y_1415_,
        v___y_1416_,
        v___y_1417_,
        v___y_1418_,
    );
    return v___x_1420_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(
    mut v_00_u03b1_1421_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1422_: *mut crate::leanh::LeanObject,
    mut v_x_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(
        v_00_u03b1_1421_,
        v_mvarId_1422_,
        v_x_1423_,
        v___y_1424_,
        v___y_1425_,
        v___y_1426_,
        v___y_1427_,
    );
    crate::leanh::lean_dec(v___y_1427_);
    crate::leanh::lean_dec_ref(v___y_1426_);
    crate::leanh::lean_dec(v___y_1425_);
    crate::leanh::lean_dec_ref(v___y_1424_);
    return v_res_1429_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(
    mut v_msgData_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = lean_st_ref_get(v___y_1434_);
    v_env_1437_ = crate::leanh::lean_ctor_get(v___x_1436_, 0);
    crate::leanh::lean_inc_ref(v_env_1437_);
    crate::leanh::lean_dec(v___x_1436_);
    v___x_1438_ = lean_st_ref_get(v___y_1432_);
    v_mctx_1439_ = crate::leanh::lean_ctor_get(v___x_1438_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1439_);
    crate::leanh::lean_dec(v___x_1438_);
    v_lctx_1440_ = crate::leanh::lean_ctor_get(v___y_1431_, 2);
    v_options_1441_ = crate::leanh::lean_ctor_get(v___y_1433_, 2);
    crate::leanh::lean_inc_ref(v_options_1441_);
    crate::leanh::lean_inc_ref(v_lctx_1440_);
    v___x_1442_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1442_, 0, v_env_1437_);
    crate::leanh::lean_ctor_set(v___x_1442_, 1, v_mctx_1439_);
    crate::leanh::lean_ctor_set(v___x_1442_, 2, v_lctx_1440_);
    crate::leanh::lean_ctor_set(v___x_1442_, 3, v_options_1441_);
    v___x_1443_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1442_);
    crate::leanh::lean_ctor_set(v___x_1443_, 1, v_msgData_1430_);
    v___x_1444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1443_);
    return v___x_1444_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(
    mut v_msgData_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msgData_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
    crate::leanh::lean_dec(v___y_1449_);
    crate::leanh::lean_dec_ref(v___y_1448_);
    crate::leanh::lean_dec(v___y_1447_);
    crate::leanh::lean_dec_ref(v___y_1446_);
    return v_res_1451_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(
    mut v_msg_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1458_ = crate::leanh::lean_ctor_get(v___y_1455_, 5);
                v___x_1459_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msg_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
                v_a_1460_ = crate::leanh::lean_ctor_get(v___x_1459_, 0);
                v_isSharedCheck_1468_ = (!crate::leanh::lean_is_exclusive(v___x_1459_)) as u8;
                if v_isSharedCheck_1468_ == 0 {
                    v___x_1462_ = v___x_1459_;
                    v_isShared_1463_ = v_isSharedCheck_1468_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1460_);
                    crate::leanh::lean_dec(v___x_1459_);
                    v___x_1462_ = crate::leanh::lean_box(0);
                    v_isShared_1463_ = v_isSharedCheck_1468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1458_);
                v___x_1464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1464_, 0, v_ref_1458_);
                crate::leanh::lean_ctor_set(v___x_1464_, 1, v_a_1460_);
                if v_isShared_1463_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1462_, 1);
                    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1464_);
                    v___x_1466_ = v___x_1462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
                    v___x_1466_ = v_reuseFailAlloc_1467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(
    mut v_msg_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(
        v_msg_1469_,
        v___y_1470_,
        v___y_1471_,
        v___y_1472_,
        v___y_1473_,
    );
    crate::leanh::lean_dec(v___y_1473_);
    crate::leanh::lean_dec_ref(v___y_1472_);
    crate::leanh::lean_dec(v___y_1471_);
    crate::leanh::lean_dec_ref(v___y_1470_);
    return v_res_1475_;
}
pub unsafe fn _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0;
    v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__0(
    mut v_x_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once),
        _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1,
    );
    v___x_1490_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(
        v___x_1489_,
        v___y_1484_,
        v___y_1485_,
        v___y_1486_,
        v___y_1487_,
    );
    return v___x_1490_;
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(
    mut v_x_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
    mut v___y_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_Elab_Rewrites_evalExact___lam__0(
        v_x_1491_,
        v___y_1492_,
        v___y_1493_,
        v___y_1494_,
        v___y_1495_,
        v___y_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
    );
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v___y_1497_);
    crate::leanh::lean_dec_ref(v___y_1496_);
    crate::leanh::lean_dec(v___y_1495_);
    crate::leanh::lean_dec_ref(v___y_1494_);
    crate::leanh::lean_dec(v___y_1493_);
    crate::leanh::lean_dec_ref(v___y_1492_);
    crate::leanh::lean_dec(v_x_1491_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__1(
    mut v_eqProof_1502_: *mut crate::leanh::LeanObject,
    mut v___x_1503_: *mut crate::leanh::LeanObject,
    mut v_eNew_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_f_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
    mut v___y_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1512_ = l_Lean_Meta_mkEqMP(
                    v_eqProof_1502_,
                    v___x_1503_,
                    v___y_1507_,
                    v___y_1508_,
                    v___y_1509_,
                    v___y_1510_,
                );
                if crate::leanh::lean_obj_tag(v___x_1512_) == 0 {
                    v_a_1513_ = crate::leanh::lean_ctor_get(v___x_1512_, 0);
                    crate::leanh::lean_inc(v_a_1513_);
                    crate::leanh::lean_dec_ref_known(v___x_1512_, 1);
                    v___x_1514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1514_, 0, v_eNew_1504_);
                    v___x_1515_ = crate::leanh::lean_box(0);
                    v___x_1516_ = l_Lean_MVarId_replace(
                        v_a_1505_,
                        v_f_1506_,
                        v_a_1513_,
                        v___x_1514_,
                        v___x_1515_,
                        v___y_1507_,
                        v___y_1508_,
                        v___y_1509_,
                        v___y_1510_,
                    );
                    return v___x_1516_;
                } else {
                    crate::leanh::lean_dec(v_f_1506_);
                    crate::leanh::lean_dec(v_a_1505_);
                    crate::leanh::lean_dec_ref(v_eNew_1504_);
                    v_a_1517_ = crate::leanh::lean_ctor_get(v___x_1512_, 0);
                    v_isSharedCheck_1524_ = (!crate::leanh::lean_is_exclusive(v___x_1512_)) as u8;
                    if v_isSharedCheck_1524_ == 0 {
                        v___x_1519_ = v___x_1512_;
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1517_);
                        crate::leanh::lean_dec(v___x_1512_);
                        v___x_1519_ = crate::leanh::lean_box(0);
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1520_ == 0 {
                    v___x_1522_ = v___x_1519_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
                    v___x_1522_ = v_reuseFailAlloc_1523_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(
    mut v_eqProof_1525_: *mut crate::leanh::LeanObject,
    mut v___x_1526_: *mut crate::leanh::LeanObject,
    mut v_eNew_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
    mut v_f_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Lean_Elab_Rewrites_evalExact___lam__1(
        v_eqProof_1525_,
        v___x_1526_,
        v_eNew_1527_,
        v_a_1528_,
        v_f_1529_,
        v___y_1530_,
        v___y_1531_,
        v___y_1532_,
        v___y_1533_,
    );
    crate::leanh::lean_dec(v___y_1533_);
    crate::leanh::lean_dec_ref(v___y_1532_);
    crate::leanh::lean_dec(v___y_1531_);
    crate::leanh::lean_dec_ref(v___y_1530_);
    return v_res_1535_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(
    mut v_result_1536_: *mut crate::leanh::LeanObject,
    mut v_expr_1537_: *mut crate::leanh::LeanObject,
    mut v_symm_1538_: u8,
    mut v_f_1539_: *mut crate::leanh::LeanObject,
    mut v_tk_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
    mut v___y_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
    mut v___y_1544_: *mut crate::leanh::LeanObject,
    mut v___y_1545_: *mut crate::leanh::LeanObject,
    mut v___y_1546_: *mut crate::leanh::LeanObject,
    mut v___y_1547_: *mut crate::leanh::LeanObject,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eNew_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1550_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v___y_1542_,
                    v___y_1544_,
                    v___y_1546_,
                    v___y_1548_,
                );
                if crate::leanh::lean_obj_tag(v___x_1550_) == 0 {
                    v_a_1551_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    crate::leanh::lean_inc(v_a_1551_);
                    crate::leanh::lean_dec_ref_known(v___x_1550_, 1);
                    v_ref_1552_ = crate::leanh::lean_ctor_get(v___y_1547_, 5);
                    v_eNew_1553_ = crate::leanh::lean_ctor_get(v_result_1536_, 0);
                    v___x_1554_ = crate::leanh::lean_box((v_symm_1538_) as usize);
                    v___x_1555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1555_, 0, v_expr_1537_);
                    crate::leanh::lean_ctor_set(v___x_1555_, 1, v___x_1554_);
                    v___x_1556_ = crate::leanh::lean_box(0);
                    v___x_1557_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1557_, 0, v___x_1555_);
                    crate::leanh::lean_ctor_set(v___x_1557_, 1, v___x_1556_);
                    crate::leanh::lean_inc_ref(v_eNew_1553_);
                    v___x_1558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1558_, 0, v_eNew_1553_);
                    v___x_1559_ = l_Lean_Expr_fvar___override(v_f_1539_);
                    v___x_1560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1560_, 0, v___x_1559_);
                    crate::leanh::lean_inc(v_ref_1552_);
                    v___x_1561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1561_, 0, v_ref_1552_);
                    v___x_1562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1562_, 0, v_a_1551_);
                    v___x_1563_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(
                        v_tk_1540_,
                        v___x_1557_,
                        v___x_1558_,
                        v___x_1560_,
                        v___x_1561_,
                        v___x_1562_,
                        v___y_1541_,
                        v___y_1542_,
                        v___y_1543_,
                        v___y_1544_,
                        v___y_1545_,
                        v___y_1546_,
                        v___y_1547_,
                        v___y_1548_,
                    );
                    return v___x_1563_;
                } else {
                    crate::leanh::lean_dec(v_tk_1540_);
                    crate::leanh::lean_dec(v_f_1539_);
                    crate::leanh::lean_dec_ref(v_expr_1537_);
                    v_a_1564_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1571_ = (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v___x_1566_ = v___x_1550_;
                        v_isShared_1567_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1564_);
                        crate::leanh::lean_dec(v___x_1550_);
                        v___x_1566_ = crate::leanh::lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1567_ == 0 {
                    v___x_1569_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
                    v___x_1569_ = v_reuseFailAlloc_1570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(
    mut v_result_1572_: *mut crate::leanh::LeanObject,
    mut v_expr_1573_: *mut crate::leanh::LeanObject,
    mut v_symm_1574_: *mut crate::leanh::LeanObject,
    mut v_f_1575_: *mut crate::leanh::LeanObject,
    mut v_tk_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
    mut v___y_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
    mut v___y_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_symm_boxed_1586_: u8 = 0;
    let mut v_res_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_symm_boxed_1586_ = (crate::leanh::lean_unbox(v_symm_1574_) as u8);
    v_res_1587_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(
            v_result_1572_,
            v_expr_1573_,
            v_symm_boxed_1586_,
            v_f_1575_,
            v_tk_1576_,
            v___y_1577_,
            v___y_1578_,
            v___y_1579_,
            v___y_1580_,
            v___y_1581_,
            v___y_1582_,
            v___y_1583_,
            v___y_1584_,
        );
    crate::leanh::lean_dec(v___y_1584_);
    crate::leanh::lean_dec_ref(v___y_1583_);
    crate::leanh::lean_dec(v___y_1582_);
    crate::leanh::lean_dec_ref(v___y_1581_);
    crate::leanh::lean_dec(v___y_1580_);
    crate::leanh::lean_dec_ref(v___y_1579_);
    crate::leanh::lean_dec(v___y_1578_);
    crate::leanh::lean_dec_ref(v___y_1577_);
    crate::leanh::lean_dec_ref(v_result_1572_);
    return v_res_1587_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(
    mut v_f_1588_: *mut crate::leanh::LeanObject,
    mut v_tk_1589_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1590_: *mut crate::leanh::LeanObject,
    mut v_b_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_symm_1605_: u8 = 0;
    let mut v_result_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1590_) == 0 {
                    crate::leanh::lean_dec(v_tk_1589_);
                    crate::leanh::lean_dec(v_f_1588_);
                    v___x_1601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1601_, 0, v_b_1591_);
                    return v___x_1601_;
                } else {
                    v_head_1602_ = crate::leanh::lean_ctor_get(v_as_x27_1590_, 0);
                    v_tail_1603_ = crate::leanh::lean_ctor_get(v_as_x27_1590_, 1);
                    v_expr_1604_ = crate::leanh::lean_ctor_get(v_head_1602_, 0);
                    v_symm_1605_ = crate::leanh::lean_ctor_get_uint8(
                        v_head_1602_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_result_1606_ = crate::leanh::lean_ctor_get(v_head_1602_, 2);
                    v_mctx_1607_ = crate::leanh::lean_ctor_get(v_head_1602_, 3);
                    v___x_1608_ = crate::leanh::lean_box((v_symm_1605_) as usize);
                    crate::leanh::lean_inc(v_tk_1589_);
                    crate::leanh::lean_inc(v_f_1588_);
                    crate::leanh::lean_inc_ref(v_expr_1604_);
                    crate::leanh::lean_inc_ref(v_result_1606_);
                    v___f_1609_ = crate::leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 5);
                    crate::leanh::lean_closure_set(v___f_1609_, 0, v_result_1606_);
                    crate::leanh::lean_closure_set(v___f_1609_, 1, v_expr_1604_);
                    crate::leanh::lean_closure_set(v___f_1609_, 2, v___x_1608_);
                    crate::leanh::lean_closure_set(v___f_1609_, 3, v_f_1588_);
                    crate::leanh::lean_closure_set(v___f_1609_, 4, v_tk_1589_);
                    crate::leanh::lean_inc_ref(v_mctx_1607_);
                    v___x_1610_ =
                        l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(
                            v_mctx_1607_,
                            v___f_1609_,
                            v___y_1592_,
                            v___y_1593_,
                            v___y_1594_,
                            v___y_1595_,
                            v___y_1596_,
                            v___y_1597_,
                            v___y_1598_,
                            v___y_1599_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1610_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1610_, 1);
                        v___x_1611_ = crate::leanh::lean_box(0);
                        v_as_x27_1590_ = v_tail_1603_;
                        v_b_1591_ = v___x_1611_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tk_1589_);
                        crate::leanh::lean_dec(v_f_1588_);
                        return v___x_1610_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(
    mut v_f_1613_: *mut crate::leanh::LeanObject,
    mut v_tk_1614_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1615_: *mut crate::leanh::LeanObject,
    mut v_b_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(
        v_f_1613_,
        v_tk_1614_,
        v_as_x27_1615_,
        v_b_1616_,
        v___y_1617_,
        v___y_1618_,
        v___y_1619_,
        v___y_1620_,
        v___y_1621_,
        v___y_1622_,
        v___y_1623_,
        v___y_1624_,
    );
    crate::leanh::lean_dec(v___y_1624_);
    crate::leanh::lean_dec_ref(v___y_1623_);
    crate::leanh::lean_dec(v___y_1622_);
    crate::leanh::lean_dec_ref(v___y_1621_);
    crate::leanh::lean_dec(v___y_1620_);
    crate::leanh::lean_dec_ref(v___y_1619_);
    crate::leanh::lean_dec(v___y_1618_);
    crate::leanh::lean_dec_ref(v___y_1617_);
    crate::leanh::lean_dec(v_as_x27_1615_);
    return v_res_1626_;
}
pub unsafe fn _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2;
    v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__2(
    mut v_a_1633_: *mut crate::leanh::LeanObject,
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v_tk_1636_: *mut crate::leanh::LeanObject,
    mut v___x_1637_: *mut crate::leanh::LeanObject,
    mut v___x_1638_: *mut crate::leanh::LeanObject,
    mut v_f_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1653_: u8 = 0;
    let mut v_val_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eNew_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqProof_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1711_: u8 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_reuseFailAlloc_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_unused_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1722_: u8 = 0;
    let mut v_unused_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut v_a_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_a_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1756_: u8 = 0;
    let mut v_a_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_a_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1777_: u8 = 0;
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_f_1639_);
                v___x_1649_ = l_Lean_FVarId_findDecl_x3f___redArg(v_f_1639_, v___y_1644_);
                if crate::leanh::lean_obj_tag(v___x_1649_) == 0 {
                    v_a_1650_ = crate::leanh::lean_ctor_get(v___x_1649_, 0);
                    v_isSharedCheck_1773_ = (!crate::leanh::lean_is_exclusive(v___x_1649_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v___x_1652_ = v___x_1649_;
                        v_isShared_1653_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1650_);
                        crate::leanh::lean_dec(v___x_1649_);
                        v___x_1652_ = crate::leanh::lean_box(0);
                        v_isShared_1653_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1639_);
                    crate::leanh::lean_dec(v___x_1638_);
                    crate::leanh::lean_dec(v_tk_1636_);
                    crate::leanh::lean_dec(v_a_1634_);
                    crate::leanh::lean_dec(v_a_1633_);
                    v_a_1774_ = crate::leanh::lean_ctor_get(v___x_1649_, 0);
                    v_isSharedCheck_1781_ = (!crate::leanh::lean_is_exclusive(v___x_1649_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v___x_1776_ = v___x_1649_;
                        v_isShared_1777_ = v_isSharedCheck_1781_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1774_);
                        crate::leanh::lean_dec(v___x_1649_);
                        v___x_1776_ = crate::leanh::lean_box(0);
                        v_isShared_1777_ = v_isSharedCheck_1781_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1650_) == 1 {
                    v_val_1654_ = crate::leanh::lean_ctor_get(v_a_1650_, 0);
                    crate::leanh::lean_inc(v_val_1654_);
                    crate::leanh::lean_dec_ref_known(v_a_1650_, 1);
                    v___x_1655_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1654_);
                    crate::leanh::lean_dec(v_val_1654_);
                    if v___x_1655_ == 0 {
                        crate::leanh::lean_del_object(v___x_1652_);
                        crate::leanh::lean_inc(v_f_1639_);
                        v___x_1656_ = l_Lean_FVarId_getType___redArg(
                            v_f_1639_,
                            v___y_1644_,
                            v___y_1646_,
                            v___y_1647_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1656_) == 0 {
                            v_a_1657_ = crate::leanh::lean_ctor_get(v___x_1656_, 0);
                            crate::leanh::lean_inc(v_a_1657_);
                            crate::leanh::lean_dec_ref_known(v___x_1656_, 1);
                            v___x_1658_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_1657_, v___y_1645_);
                            v_a_1659_ = crate::leanh::lean_ctor_get(v___x_1658_, 0);
                            crate::leanh::lean_inc(v_a_1659_);
                            crate::leanh::lean_dec_ref(v___x_1658_);
                            v___x_1660_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_f_1639_);
                            v___x_1661_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1661_, 0, v_f_1639_);
                            crate::leanh::lean_ctor_set(v___x_1661_, 1, v___x_1660_);
                            v___x_1662_ = l_Lean_Meta_Rewrites_localHypotheses(
                                v___x_1661_,
                                v___y_1644_,
                                v___y_1645_,
                                v___y_1646_,
                                v___y_1647_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_1661_, 2);
                            if crate::leanh::lean_obj_tag(v___x_1662_) == 0 {
                                v_a_1663_ = crate::leanh::lean_ctor_get(v___x_1662_, 0);
                                crate::leanh::lean_inc(v_a_1663_);
                                crate::leanh::lean_dec_ref_known(v___x_1662_, 1);
                                v___x_1664_ = 2;
                                v___x_1665_ = crate::leanh::lean_unsigned_to_nat(20);
                                v___x_1666_ = crate::leanh::lean_unsigned_to_nat(10);
                                crate::leanh::lean_inc(v_a_1634_);
                                v___x_1667_ = l_Lean_Meta_Rewrites_findRewrites(
                                    v_a_1663_,
                                    v_a_1633_,
                                    v_a_1634_,
                                    v_a_1659_,
                                    v___y_1635_,
                                    v___x_1664_,
                                    v___x_1655_,
                                    v___x_1665_,
                                    v___x_1666_,
                                    v___y_1644_,
                                    v___y_1645_,
                                    v___y_1646_,
                                    v___y_1647_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1667_) == 0 {
                                    v_a_1668_ = crate::leanh::lean_ctor_get(v___x_1667_, 0);
                                    crate::leanh::lean_inc(v_a_1668_);
                                    crate::leanh::lean_dec_ref_known(v___x_1667_, 1);
                                    v___x_1724_ =
                                        l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1;
                                    v___x_1725_ = l_Lean_reportOutOfHeartbeats(
                                        v___x_1724_,
                                        v_tk_1636_,
                                        v___x_1637_,
                                        v___y_1646_,
                                        v___y_1647_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1725_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1725_, 1);
                                        v___x_1726_ = l_List_isEmpty___redArg(v_a_1668_);
                                        if v___x_1726_ == 0 {
                                            v___y_1670_ = v___y_1640_;
                                            v___y_1671_ = v___y_1641_;
                                            v___y_1672_ = v___y_1642_;
                                            v___y_1673_ = v___y_1643_;
                                            v___y_1674_ = v___y_1644_;
                                            v___y_1675_ = v___y_1645_;
                                            v___y_1676_ = v___y_1646_;
                                            v___y_1677_ = v___y_1647_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_1668_);
                                            crate::leanh::lean_dec(v___x_1638_);
                                            crate::leanh::lean_dec(v_tk_1636_);
                                            crate::leanh::lean_dec(v_a_1634_);
                                            v___x_1727_ = l_Lean_FVarId_getUserName___redArg(
                                                v_f_1639_,
                                                v___y_1644_,
                                                v___y_1646_,
                                                v___y_1647_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_1727_) == 0 {
                                                v_a_1728_ =
                                                    crate::leanh::lean_ctor_get(v___x_1727_, 0);
                                                crate::leanh::lean_inc(v_a_1728_);
                                                crate::leanh::lean_dec_ref_known(v___x_1727_, 1);
                                                v___x_1729_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_once), _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3);
                                                v___x_1730_ = l_Lean_MessageData_ofName(v_a_1728_);
                                                v___x_1731_ =
                                                    crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_1731_,
                                                    0,
                                                    v___x_1729_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_1731_,
                                                    1,
                                                    v___x_1730_,
                                                );
                                                v___x_1732_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_1731_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
                                                return v___x_1732_;
                                            } else {
                                                v_a_1733_ =
                                                    crate::leanh::lean_ctor_get(v___x_1727_, 0);
                                                v_isSharedCheck_1740_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1727_))
                                                        as u8;
                                                if v_isSharedCheck_1740_ == 0 {
                                                    v___x_1735_ = v___x_1727_;
                                                    v_isShared_1736_ = v_isSharedCheck_1740_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1733_);
                                                    crate::leanh::lean_dec(v___x_1727_);
                                                    v___x_1735_ = crate::leanh::lean_box(0);
                                                    v_isShared_1736_ = v_isSharedCheck_1740_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1668_);
                                        crate::leanh::lean_dec(v_f_1639_);
                                        crate::leanh::lean_dec(v___x_1638_);
                                        crate::leanh::lean_dec(v_tk_1636_);
                                        crate::leanh::lean_dec(v_a_1634_);
                                        return v___x_1725_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_f_1639_);
                                    crate::leanh::lean_dec(v___x_1638_);
                                    crate::leanh::lean_dec(v_tk_1636_);
                                    crate::leanh::lean_dec(v_a_1634_);
                                    v_a_1741_ = crate::leanh::lean_ctor_get(v___x_1667_, 0);
                                    v_isSharedCheck_1748_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1667_)) as u8;
                                    if v_isSharedCheck_1748_ == 0 {
                                        v___x_1743_ = v___x_1667_;
                                        v_isShared_1744_ = v_isSharedCheck_1748_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1741_);
                                        crate::leanh::lean_dec(v___x_1667_);
                                        v___x_1743_ = crate::leanh::lean_box(0);
                                        v_isShared_1744_ = v_isSharedCheck_1748_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1659_);
                                crate::leanh::lean_dec(v_f_1639_);
                                crate::leanh::lean_dec(v___x_1638_);
                                crate::leanh::lean_dec(v_tk_1636_);
                                crate::leanh::lean_dec(v_a_1634_);
                                crate::leanh::lean_dec(v_a_1633_);
                                v_a_1749_ = crate::leanh::lean_ctor_get(v___x_1662_, 0);
                                v_isSharedCheck_1756_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1662_)) as u8;
                                if v_isSharedCheck_1756_ == 0 {
                                    v___x_1751_ = v___x_1662_;
                                    v_isShared_1752_ = v_isSharedCheck_1756_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1749_);
                                    crate::leanh::lean_dec(v___x_1662_);
                                    v___x_1751_ = crate::leanh::lean_box(0);
                                    v_isShared_1752_ = v_isSharedCheck_1756_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_f_1639_);
                            crate::leanh::lean_dec(v___x_1638_);
                            crate::leanh::lean_dec(v_tk_1636_);
                            crate::leanh::lean_dec(v_a_1634_);
                            crate::leanh::lean_dec(v_a_1633_);
                            v_a_1757_ = crate::leanh::lean_ctor_get(v___x_1656_, 0);
                            v_isSharedCheck_1764_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1656_)) as u8;
                            if v_isSharedCheck_1764_ == 0 {
                                v___x_1759_ = v___x_1656_;
                                v_isShared_1760_ = v_isSharedCheck_1764_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1757_);
                                crate::leanh::lean_dec(v___x_1656_);
                                v___x_1759_ = crate::leanh::lean_box(0);
                                v_isShared_1760_ = v_isSharedCheck_1764_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_f_1639_);
                        crate::leanh::lean_dec(v___x_1638_);
                        crate::leanh::lean_dec(v_tk_1636_);
                        crate::leanh::lean_dec(v_a_1634_);
                        crate::leanh::lean_dec(v_a_1633_);
                        v___x_1765_ = crate::leanh::lean_box(0);
                        if v_isShared_1653_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1765_);
                            v___x_1767_ = v___x_1652_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_1768_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
                            v___x_1767_ = v_reuseFailAlloc_1768_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1650_);
                    crate::leanh::lean_dec(v_f_1639_);
                    crate::leanh::lean_dec(v___x_1638_);
                    crate::leanh::lean_dec(v_tk_1636_);
                    crate::leanh::lean_dec(v_a_1634_);
                    crate::leanh::lean_dec(v_a_1633_);
                    v___x_1769_ = crate::leanh::lean_box(0);
                    if v_isShared_1653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1769_);
                        v___x_1771_ = v___x_1652_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
                        v___x_1771_ = v_reuseFailAlloc_1772_;
                        state = 18;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1678_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_f_1639_);
                v___x_1679_ =
                    l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(
                        v_f_1639_,
                        v_tk_1636_,
                        v_a_1668_,
                        v___x_1678_,
                        v___y_1670_,
                        v___y_1671_,
                        v___y_1672_,
                        v___y_1673_,
                        v___y_1674_,
                        v___y_1675_,
                        v___y_1676_,
                        v___y_1677_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1679_) == 0 {
                    v_isSharedCheck_1722_ = (!crate::leanh::lean_is_exclusive(v___x_1679_)) as u8;
                    if v_isSharedCheck_1722_ == 0 {
                        v_unused_1723_ = crate::leanh::lean_ctor_get(v___x_1679_, 0);
                        crate::leanh::lean_dec(v_unused_1723_);
                        v___x_1681_ = v___x_1679_;
                        v_isShared_1682_ = v_isSharedCheck_1722_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1679_);
                        v___x_1681_ = crate::leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1722_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1668_);
                    crate::leanh::lean_dec(v_f_1639_);
                    crate::leanh::lean_dec(v___x_1638_);
                    crate::leanh::lean_dec(v_a_1634_);
                    return v___x_1679_;
                }
            }
            3 => {
                v___x_1683_ = l_List_get_x3fInternal___redArg(v_a_1668_, v___x_1638_);
                crate::leanh::lean_dec(v_a_1668_);
                if crate::leanh::lean_obj_tag(v___x_1683_) == 1 {
                    crate::leanh::lean_del_object(v___x_1681_);
                    v_val_1684_ = crate::leanh::lean_ctor_get(v___x_1683_, 0);
                    crate::leanh::lean_inc(v_val_1684_);
                    crate::leanh::lean_dec_ref_known(v___x_1683_, 1);
                    v___x_1685_ = lean_st_ref_take(v___y_1675_);
                    v_result_1686_ = crate::leanh::lean_ctor_get(v_val_1684_, 2);
                    crate::leanh::lean_inc_ref(v_result_1686_);
                    v_mctx_1687_ = crate::leanh::lean_ctor_get(v_val_1684_, 3);
                    crate::leanh::lean_inc_ref(v_mctx_1687_);
                    crate::leanh::lean_dec(v_val_1684_);
                    v_cache_1688_ = crate::leanh::lean_ctor_get(v___x_1685_, 1);
                    v_zetaDeltaFVarIds_1689_ = crate::leanh::lean_ctor_get(v___x_1685_, 2);
                    v_postponed_1690_ = crate::leanh::lean_ctor_get(v___x_1685_, 3);
                    v_diag_1691_ = crate::leanh::lean_ctor_get(v___x_1685_, 4);
                    v_isSharedCheck_1717_ = (!crate::leanh::lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1717_ == 0 {
                        v_unused_1718_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                        crate::leanh::lean_dec(v_unused_1718_);
                        v___x_1693_ = v___x_1685_;
                        v_isShared_1694_ = v_isSharedCheck_1717_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1691_);
                        crate::leanh::lean_inc(v_postponed_1690_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1689_);
                        crate::leanh::lean_inc(v_cache_1688_);
                        crate::leanh::lean_dec(v___x_1685_);
                        v___x_1693_ = crate::leanh::lean_box(0);
                        v_isShared_1694_ = v_isSharedCheck_1717_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1683_);
                    crate::leanh::lean_dec(v_f_1639_);
                    crate::leanh::lean_dec(v_a_1634_);
                    if v_isShared_1682_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1678_);
                        v___x_1720_ = v___x_1681_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1721_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1678_);
                        v___x_1720_ = v_reuseFailAlloc_1721_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1694_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v_mctx_1687_);
                    v___x_1696_ = v___x_1693_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_mctx_1687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_cache_1688_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1716_,
                        2,
                        v_zetaDeltaFVarIds_1689_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_postponed_1690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 4, v_diag_1691_);
                    v___x_1696_ = v_reuseFailAlloc_1716_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1697_ = lean_st_ref_set(v___y_1675_, v___x_1696_);
                v_eNew_1698_ = crate::leanh::lean_ctor_get(v_result_1686_, 0);
                crate::leanh::lean_inc_ref(v_eNew_1698_);
                v_eqProof_1699_ = crate::leanh::lean_ctor_get(v_result_1686_, 1);
                crate::leanh::lean_inc_ref(v_eqProof_1699_);
                v_mvarIds_1700_ = crate::leanh::lean_ctor_get(v_result_1686_, 2);
                crate::leanh::lean_inc(v_mvarIds_1700_);
                crate::leanh::lean_dec_ref(v_result_1686_);
                crate::leanh::lean_inc(v_f_1639_);
                v___x_1701_ = l_Lean_mkFVar(v_f_1639_);
                crate::leanh::lean_inc(v_a_1634_);
                v___f_1702_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Rewrites_evalExact___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_1702_, 0, v_eqProof_1699_);
                crate::leanh::lean_closure_set(v___f_1702_, 1, v___x_1701_);
                crate::leanh::lean_closure_set(v___f_1702_, 2, v_eNew_1698_);
                crate::leanh::lean_closure_set(v___f_1702_, 3, v_a_1634_);
                crate::leanh::lean_closure_set(v___f_1702_, 4, v_f_1639_);
                v___x_1703_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_a_1634_, v___f_1702_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
                if crate::leanh::lean_obj_tag(v___x_1703_) == 0 {
                    v_a_1704_ = crate::leanh::lean_ctor_get(v___x_1703_, 0);
                    crate::leanh::lean_inc(v_a_1704_);
                    crate::leanh::lean_dec_ref_known(v___x_1703_, 1);
                    v_mvarId_1705_ = crate::leanh::lean_ctor_get(v_a_1704_, 1);
                    crate::leanh::lean_inc(v_mvarId_1705_);
                    crate::leanh::lean_dec(v_a_1704_);
                    v___x_1706_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1706_, 0, v_mvarId_1705_);
                    crate::leanh::lean_ctor_set(v___x_1706_, 1, v_mvarIds_1700_);
                    v___x_1707_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1706_,
                        v___y_1671_,
                        v___y_1674_,
                        v___y_1675_,
                        v___y_1676_,
                        v___y_1677_,
                    );
                    return v___x_1707_;
                } else {
                    crate::leanh::lean_dec(v_mvarIds_1700_);
                    v_a_1708_ = crate::leanh::lean_ctor_get(v___x_1703_, 0);
                    v_isSharedCheck_1715_ = (!crate::leanh::lean_is_exclusive(v___x_1703_)) as u8;
                    if v_isSharedCheck_1715_ == 0 {
                        v___x_1710_ = v___x_1703_;
                        v_isShared_1711_ = v_isSharedCheck_1715_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1708_);
                        crate::leanh::lean_dec(v___x_1703_);
                        v___x_1710_ = crate::leanh::lean_box(0);
                        v_isShared_1711_ = v_isSharedCheck_1715_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1711_ == 0 {
                    v___x_1713_ = v___x_1710_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
                    v___x_1713_ = v_reuseFailAlloc_1714_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1713_;
            }
            8 => {
                return v___x_1720_;
            }
            9 => {
                if v_isShared_1736_ == 0 {
                    v___x_1738_ = v___x_1735_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
                    v___x_1738_ = v_reuseFailAlloc_1739_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1738_;
            }
            11 => {
                if v_isShared_1744_ == 0 {
                    v___x_1746_ = v___x_1743_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
                    v___x_1746_ = v_reuseFailAlloc_1747_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1746_;
            }
            13 => {
                if v_isShared_1752_ == 0 {
                    v___x_1754_ = v___x_1751_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1755_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
                    v___x_1754_ = v_reuseFailAlloc_1755_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1754_;
            }
            15 => {
                if v_isShared_1760_ == 0 {
                    v___x_1762_ = v___x_1759_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
                    v___x_1762_ = v_reuseFailAlloc_1763_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1762_;
            }
            17 => {
                return v___x_1767_;
            }
            18 => {
                return v___x_1771_;
            }
            19 => {
                if v_isShared_1777_ == 0 {
                    v___x_1779_ = v___x_1776_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
                    v___x_1779_ = v_reuseFailAlloc_1780_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(
    mut v_a_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v_tk_1785_: *mut crate::leanh::LeanObject,
    mut v___x_1786_: *mut crate::leanh::LeanObject,
    mut v___x_1787_: *mut crate::leanh::LeanObject,
    mut v_f_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lean_Elab_Rewrites_evalExact___lam__2(
        v_a_1782_,
        v_a_1783_,
        v___y_1784_,
        v_tk_1785_,
        v___x_1786_,
        v___x_1787_,
        v_f_1788_,
        v___y_1789_,
        v___y_1790_,
        v___y_1791_,
        v___y_1792_,
        v___y_1793_,
        v___y_1794_,
        v___y_1795_,
        v___y_1796_,
    );
    crate::leanh::lean_dec(v___y_1796_);
    crate::leanh::lean_dec_ref(v___y_1795_);
    crate::leanh::lean_dec(v___y_1794_);
    crate::leanh::lean_dec_ref(v___y_1793_);
    crate::leanh::lean_dec(v___y_1792_);
    crate::leanh::lean_dec_ref(v___y_1791_);
    crate::leanh::lean_dec(v___y_1790_);
    crate::leanh::lean_dec_ref(v___y_1789_);
    crate::leanh::lean_dec(v___x_1786_);
    crate::leanh::lean_dec(v___y_1784_);
    return v_res_1798_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(
    mut v_state_1799_: *mut crate::leanh::LeanObject,
    mut v_tk_1800_: *mut crate::leanh::LeanObject,
    mut v_as_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_1801_) == 0 {
                    crate::leanh::lean_dec(v_tk_1800_);
                    crate::leanh::lean_dec_ref(v_state_1799_);
                    v___x_1811_ = crate::leanh::lean_box(0);
                    v___x_1812_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
                    return v___x_1812_;
                } else {
                    v_head_1813_ = crate::leanh::lean_ctor_get(v_as_1801_, 0);
                    crate::leanh::lean_inc(v_head_1813_);
                    v_tail_1814_ = crate::leanh::lean_ctor_get(v_as_1801_, 1);
                    crate::leanh::lean_inc(v_tail_1814_);
                    crate::leanh::lean_dec_ref_known(v_as_1801_, 2);
                    crate::leanh::lean_inc_ref(v_state_1799_);
                    v___x_1815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1815_, 0, v_state_1799_);
                    crate::leanh::lean_inc(v_tk_1800_);
                    v___x_1816_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(
                        v_tk_1800_,
                        v_head_1813_,
                        v___x_1815_,
                        v___y_1802_,
                        v___y_1803_,
                        v___y_1804_,
                        v___y_1805_,
                        v___y_1806_,
                        v___y_1807_,
                        v___y_1808_,
                        v___y_1809_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1816_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1816_, 1);
                        v_as_1801_ = v_tail_1814_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1814_);
                        crate::leanh::lean_dec(v_tk_1800_);
                        crate::leanh::lean_dec_ref(v_state_1799_);
                        return v___x_1816_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(
    mut v_state_1818_: *mut crate::leanh::LeanObject,
    mut v_tk_1819_: *mut crate::leanh::LeanObject,
    mut v_as_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(
        v_state_1818_,
        v_tk_1819_,
        v_as_1820_,
        v___y_1821_,
        v___y_1822_,
        v___y_1823_,
        v___y_1824_,
        v___y_1825_,
        v___y_1826_,
        v___y_1827_,
        v___y_1828_,
    );
    crate::leanh::lean_dec(v___y_1828_);
    crate::leanh::lean_dec_ref(v___y_1827_);
    crate::leanh::lean_dec(v___y_1826_);
    crate::leanh::lean_dec_ref(v___y_1825_);
    crate::leanh::lean_dec(v___y_1824_);
    crate::leanh::lean_dec_ref(v___y_1823_);
    crate::leanh::lean_dec(v___y_1822_);
    crate::leanh::lean_dec_ref(v___y_1821_);
    return v_res_1830_;
}
pub unsafe fn _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8;
    v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
    return v___x_1842_;
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__3(
    mut v_a_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___x_1846_: u8,
    mut v_tk_1847_: *mut crate::leanh::LeanObject,
    mut v___x_1848_: *mut crate::leanh::LeanObject,
    mut v___x_1849_: *mut crate::leanh::LeanObject,
    mut v___x_1850_: *mut crate::leanh::LeanObject,
    mut v___x_1851_: *mut crate::leanh::LeanObject,
    mut v___x_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eNew_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqProof_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1939_: u8 = 0;
    let mut v_a_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v_reuseFailAlloc_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut v_unused_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1972_: u8 = 0;
    let mut v_a_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v_a_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1843_);
                v___x_1862_ = l_Lean_MVarId_getType(
                    v_a_1843_,
                    v___y_1857_,
                    v___y_1858_,
                    v___y_1859_,
                    v___y_1860_,
                );
                if crate::leanh::lean_obj_tag(v___x_1862_) == 0 {
                    v_a_1863_ = crate::leanh::lean_ctor_get(v___x_1862_, 0);
                    crate::leanh::lean_inc(v_a_1863_);
                    crate::leanh::lean_dec_ref_known(v___x_1862_, 1);
                    v___x_1864_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_1863_, v___y_1858_);
                    v_a_1865_ = crate::leanh::lean_ctor_get(v___x_1864_, 0);
                    crate::leanh::lean_inc(v_a_1865_);
                    crate::leanh::lean_dec_ref(v___x_1864_);
                    v___x_1866_ = crate::leanh::lean_box(0);
                    v___x_1867_ = l_Lean_Meta_Rewrites_localHypotheses(
                        v___x_1866_,
                        v___y_1857_,
                        v___y_1858_,
                        v___y_1859_,
                        v___y_1860_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1867_) == 0 {
                        v_a_1868_ = crate::leanh::lean_ctor_get(v___x_1867_, 0);
                        crate::leanh::lean_inc(v_a_1868_);
                        crate::leanh::lean_dec_ref_known(v___x_1867_, 1);
                        v___x_1869_ = 2;
                        v___x_1870_ = crate::leanh::lean_unsigned_to_nat(20);
                        v___x_1871_ = crate::leanh::lean_unsigned_to_nat(10);
                        crate::leanh::lean_inc(v_a_1843_);
                        v___x_1872_ = l_Lean_Meta_Rewrites_findRewrites(
                            v_a_1868_,
                            v_a_1844_,
                            v_a_1843_,
                            v_a_1865_,
                            v___y_1845_,
                            v___x_1869_,
                            v___x_1846_,
                            v___x_1870_,
                            v___x_1871_,
                            v___y_1857_,
                            v___y_1858_,
                            v___y_1859_,
                            v___y_1860_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1872_) == 0 {
                            v_a_1873_ = crate::leanh::lean_ctor_get(v___x_1872_, 0);
                            crate::leanh::lean_inc(v_a_1873_);
                            crate::leanh::lean_dec_ref_known(v___x_1872_, 1);
                            v___x_1960_ = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1;
                            v___x_1961_ = l_Lean_reportOutOfHeartbeats(
                                v___x_1960_,
                                v_tk_1847_,
                                v___x_1848_,
                                v___y_1859_,
                                v___y_1860_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1961_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1961_, 1);
                                v___x_1962_ = l_List_isEmpty___redArg(v_a_1873_);
                                if v___x_1962_ == 0 {
                                    v___y_1875_ = v___y_1853_;
                                    v___y_1876_ = v___y_1854_;
                                    v___y_1877_ = v___y_1855_;
                                    v___y_1878_ = v___y_1856_;
                                    v___y_1879_ = v___y_1857_;
                                    v___y_1880_ = v___y_1858_;
                                    v___y_1881_ = v___y_1859_;
                                    v___y_1882_ = v___y_1860_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_1873_);
                                    crate::leanh::lean_dec_ref(v___x_1852_);
                                    crate::leanh::lean_dec_ref(v___x_1851_);
                                    crate::leanh::lean_dec_ref(v___x_1850_);
                                    crate::leanh::lean_dec(v___x_1849_);
                                    crate::leanh::lean_dec(v_tk_1847_);
                                    crate::leanh::lean_dec(v_a_1843_);
                                    v___x_1963_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9_once), _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9);
                                    v___x_1964_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_1963_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
                                    return v___x_1964_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1873_);
                                crate::leanh::lean_dec_ref(v___x_1852_);
                                crate::leanh::lean_dec_ref(v___x_1851_);
                                crate::leanh::lean_dec_ref(v___x_1850_);
                                crate::leanh::lean_dec(v___x_1849_);
                                crate::leanh::lean_dec(v_tk_1847_);
                                crate::leanh::lean_dec(v_a_1843_);
                                return v___x_1961_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1852_);
                            crate::leanh::lean_dec_ref(v___x_1851_);
                            crate::leanh::lean_dec_ref(v___x_1850_);
                            crate::leanh::lean_dec(v___x_1849_);
                            crate::leanh::lean_dec(v_tk_1847_);
                            crate::leanh::lean_dec(v_a_1843_);
                            v_a_1965_ = crate::leanh::lean_ctor_get(v___x_1872_, 0);
                            v_isSharedCheck_1972_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1872_)) as u8;
                            if v_isSharedCheck_1972_ == 0 {
                                v___x_1967_ = v___x_1872_;
                                v_isShared_1968_ = v_isSharedCheck_1972_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1965_);
                                crate::leanh::lean_dec(v___x_1872_);
                                v___x_1967_ = crate::leanh::lean_box(0);
                                v_isShared_1968_ = v_isSharedCheck_1972_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1865_);
                        crate::leanh::lean_dec_ref(v___x_1852_);
                        crate::leanh::lean_dec_ref(v___x_1851_);
                        crate::leanh::lean_dec_ref(v___x_1850_);
                        crate::leanh::lean_dec(v___x_1849_);
                        crate::leanh::lean_dec(v_tk_1847_);
                        crate::leanh::lean_dec(v_a_1844_);
                        crate::leanh::lean_dec(v_a_1843_);
                        v_a_1973_ = crate::leanh::lean_ctor_get(v___x_1867_, 0);
                        v_isSharedCheck_1980_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1867_)) as u8;
                        if v_isSharedCheck_1980_ == 0 {
                            v___x_1975_ = v___x_1867_;
                            v_isShared_1976_ = v_isSharedCheck_1980_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1973_);
                            crate::leanh::lean_dec(v___x_1867_);
                            v___x_1975_ = crate::leanh::lean_box(0);
                            v_isShared_1976_ = v_isSharedCheck_1980_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1852_);
                    crate::leanh::lean_dec_ref(v___x_1851_);
                    crate::leanh::lean_dec_ref(v___x_1850_);
                    crate::leanh::lean_dec(v___x_1849_);
                    crate::leanh::lean_dec(v_tk_1847_);
                    crate::leanh::lean_dec(v_a_1844_);
                    crate::leanh::lean_dec(v_a_1843_);
                    v_a_1981_ = crate::leanh::lean_ctor_get(v___x_1862_, 0);
                    v_isSharedCheck_1988_ = (!crate::leanh::lean_is_exclusive(v___x_1862_)) as u8;
                    if v_isSharedCheck_1988_ == 0 {
                        v___x_1983_ = v___x_1862_;
                        v_isShared_1984_ = v_isSharedCheck_1988_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1981_);
                        crate::leanh::lean_dec(v___x_1862_);
                        v___x_1983_ = crate::leanh::lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_1988_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1883_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v___y_1876_,
                    v___y_1878_,
                    v___y_1880_,
                    v___y_1882_,
                );
                if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v_a_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    crate::leanh::lean_inc(v_a_1884_);
                    crate::leanh::lean_dec_ref_known(v___x_1883_, 1);
                    v___x_1885_ = l_List_get_x3fInternal___redArg(v_a_1873_, v___x_1849_);
                    if crate::leanh::lean_obj_tag(v___x_1885_) == 1 {
                        crate::leanh::lean_dec(v_a_1884_);
                        v_val_1886_ = crate::leanh::lean_ctor_get(v___x_1885_, 0);
                        crate::leanh::lean_inc(v_val_1886_);
                        crate::leanh::lean_dec_ref_known(v___x_1885_, 1);
                        v___x_1887_ = lean_st_ref_take(v___y_1880_);
                        v_result_1888_ = crate::leanh::lean_ctor_get(v_val_1886_, 2);
                        crate::leanh::lean_inc_ref(v_result_1888_);
                        v_mctx_1889_ = crate::leanh::lean_ctor_get(v_val_1886_, 3);
                        crate::leanh::lean_inc_ref(v_mctx_1889_);
                        crate::leanh::lean_dec(v_val_1886_);
                        v_cache_1890_ = crate::leanh::lean_ctor_get(v___x_1887_, 1);
                        v_zetaDeltaFVarIds_1891_ = crate::leanh::lean_ctor_get(v___x_1887_, 2);
                        v_postponed_1892_ = crate::leanh::lean_ctor_get(v___x_1887_, 3);
                        v_diag_1893_ = crate::leanh::lean_ctor_get(v___x_1887_, 4);
                        v_isSharedCheck_1949_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1887_)) as u8;
                        if v_isSharedCheck_1949_ == 0 {
                            v_unused_1950_ = crate::leanh::lean_ctor_get(v___x_1887_, 0);
                            crate::leanh::lean_dec(v_unused_1950_);
                            v___x_1895_ = v___x_1887_;
                            v_isShared_1896_ = v_isSharedCheck_1949_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_diag_1893_);
                            crate::leanh::lean_inc(v_postponed_1892_);
                            crate::leanh::lean_inc(v_zetaDeltaFVarIds_1891_);
                            crate::leanh::lean_inc(v_cache_1890_);
                            crate::leanh::lean_dec(v___x_1887_);
                            v___x_1895_ = crate::leanh::lean_box(0);
                            v_isShared_1896_ = v_isSharedCheck_1949_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1885_);
                        crate::leanh::lean_dec_ref(v___x_1852_);
                        crate::leanh::lean_dec_ref(v___x_1851_);
                        crate::leanh::lean_dec_ref(v___x_1850_);
                        crate::leanh::lean_dec(v_a_1843_);
                        v___x_1951_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(
                            v_a_1884_,
                            v_tk_1847_,
                            v_a_1873_,
                            v___y_1875_,
                            v___y_1876_,
                            v___y_1877_,
                            v___y_1878_,
                            v___y_1879_,
                            v___y_1880_,
                            v___y_1881_,
                            v___y_1882_,
                        );
                        return v___x_1951_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1873_);
                    crate::leanh::lean_dec_ref(v___x_1852_);
                    crate::leanh::lean_dec_ref(v___x_1851_);
                    crate::leanh::lean_dec_ref(v___x_1850_);
                    crate::leanh::lean_dec(v___x_1849_);
                    crate::leanh::lean_dec(v_tk_1847_);
                    crate::leanh::lean_dec(v_a_1843_);
                    v_a_1952_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    v_isSharedCheck_1959_ = (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1959_ == 0 {
                        v___x_1954_ = v___x_1883_;
                        v_isShared_1955_ = v_isSharedCheck_1959_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1952_);
                        crate::leanh::lean_dec(v___x_1883_);
                        v___x_1954_ = crate::leanh::lean_box(0);
                        v_isShared_1955_ = v_isSharedCheck_1959_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1895_, 0, v_mctx_1889_);
                    v___x_1898_ = v___x_1895_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1948_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_mctx_1889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_cache_1890_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1948_,
                        2,
                        v_zetaDeltaFVarIds_1891_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_postponed_1892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_diag_1893_);
                    v___x_1898_ = v_reuseFailAlloc_1948_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1899_ = lean_st_ref_set(v___y_1880_, v___x_1898_);
                v___x_1900_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v___y_1876_,
                    v___y_1878_,
                    v___y_1880_,
                    v___y_1882_,
                );
                if crate::leanh::lean_obj_tag(v___x_1900_) == 0 {
                    v_a_1901_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                    crate::leanh::lean_inc(v_a_1901_);
                    crate::leanh::lean_dec_ref_known(v___x_1900_, 1);
                    v_eNew_1902_ = crate::leanh::lean_ctor_get(v_result_1888_, 0);
                    crate::leanh::lean_inc_ref(v_eNew_1902_);
                    v_eqProof_1903_ = crate::leanh::lean_ctor_get(v_result_1888_, 1);
                    crate::leanh::lean_inc_ref(v_eqProof_1903_);
                    v_mvarIds_1904_ = crate::leanh::lean_ctor_get(v_result_1888_, 2);
                    crate::leanh::lean_inc(v_mvarIds_1904_);
                    crate::leanh::lean_dec_ref(v_result_1888_);
                    v___x_1905_ = l_Lean_MVarId_replaceTargetEq(
                        v_a_1843_,
                        v_eNew_1902_,
                        v_eqProof_1903_,
                        v___y_1879_,
                        v___y_1880_,
                        v___y_1881_,
                        v___y_1882_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1905_) == 0 {
                        v_a_1906_ = crate::leanh::lean_ctor_get(v___x_1905_, 0);
                        crate::leanh::lean_inc(v_a_1906_);
                        crate::leanh::lean_dec_ref_known(v___x_1905_, 1);
                        v___x_1907_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1907_, 0, v_a_1906_);
                        crate::leanh::lean_ctor_set(v___x_1907_, 1, v_mvarIds_1904_);
                        v___x_1908_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_1907_,
                            v___y_1876_,
                            v___y_1879_,
                            v___y_1880_,
                            v___y_1881_,
                            v___y_1882_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1908_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1908_, 1);
                            v_ref_1909_ = crate::leanh::lean_ctor_get(v___y_1881_, 5);
                            v___x_1910_ = 0;
                            v___x_1911_ = l_Lean_SourceInfo_fromRef(v_ref_1909_, v___x_1910_);
                            v___x_1912_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0;
                            crate::leanh::lean_inc_ref_n(v___x_1852_, 3);
                            crate::leanh::lean_inc_ref_n(v___x_1851_, 3);
                            crate::leanh::lean_inc_ref_n(v___x_1850_, 3);
                            v___x_1913_ = l_Lean_Name_mkStr4(
                                v___x_1850_,
                                v___x_1851_,
                                v___x_1852_,
                                v___x_1912_,
                            );
                            v___x_1914_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1;
                            crate::leanh::lean_inc_n(v___x_1911_, 6);
                            v___x_1915_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1915_, 0, v___x_1911_);
                            crate::leanh::lean_ctor_set(v___x_1915_, 1, v___x_1914_);
                            v___x_1916_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2;
                            v___x_1917_ = l_Lean_Name_mkStr4(
                                v___x_1850_,
                                v___x_1851_,
                                v___x_1852_,
                                v___x_1916_,
                            );
                            v___x_1918_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3;
                            v___x_1919_ = l_Lean_Name_mkStr4(
                                v___x_1850_,
                                v___x_1851_,
                                v___x_1852_,
                                v___x_1918_,
                            );
                            v___x_1920_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5;
                            v___x_1921_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6;
                            v___x_1922_ = l_Lean_Name_mkStr4(
                                v___x_1850_,
                                v___x_1851_,
                                v___x_1852_,
                                v___x_1921_,
                            );
                            v___x_1923_ = l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7;
                            v___x_1924_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1924_, 0, v___x_1911_);
                            crate::leanh::lean_ctor_set(v___x_1924_, 1, v___x_1923_);
                            v___x_1925_ =
                                l_Lean_Syntax_node1(v___x_1911_, v___x_1922_, v___x_1924_);
                            v___x_1926_ =
                                l_Lean_Syntax_node1(v___x_1911_, v___x_1920_, v___x_1925_);
                            v___x_1927_ =
                                l_Lean_Syntax_node1(v___x_1911_, v___x_1919_, v___x_1926_);
                            v___x_1928_ =
                                l_Lean_Syntax_node1(v___x_1911_, v___x_1917_, v___x_1927_);
                            v___x_1929_ = l_Lean_Syntax_node2(
                                v___x_1911_,
                                v___x_1913_,
                                v___x_1915_,
                                v___x_1928_,
                            );
                            v___x_1930_ = l_Lean_Elab_Tactic_evalTactic(
                                v___x_1929_,
                                v___y_1875_,
                                v___y_1876_,
                                v___y_1877_,
                                v___y_1878_,
                                v___y_1879_,
                                v___y_1880_,
                                v___y_1881_,
                                v___y_1882_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1930_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1930_, 1);
                                v___x_1931_ =
                                    l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(
                                        v_a_1901_,
                                        v_tk_1847_,
                                        v_a_1873_,
                                        v___y_1875_,
                                        v___y_1876_,
                                        v___y_1877_,
                                        v___y_1878_,
                                        v___y_1879_,
                                        v___y_1880_,
                                        v___y_1881_,
                                        v___y_1882_,
                                    );
                                return v___x_1931_;
                            } else {
                                crate::leanh::lean_dec(v_a_1901_);
                                crate::leanh::lean_dec(v_a_1873_);
                                crate::leanh::lean_dec(v_tk_1847_);
                                return v___x_1930_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1901_);
                            crate::leanh::lean_dec(v_a_1873_);
                            crate::leanh::lean_dec_ref(v___x_1852_);
                            crate::leanh::lean_dec_ref(v___x_1851_);
                            crate::leanh::lean_dec_ref(v___x_1850_);
                            crate::leanh::lean_dec(v_tk_1847_);
                            return v___x_1908_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarIds_1904_);
                        crate::leanh::lean_dec(v_a_1901_);
                        crate::leanh::lean_dec(v_a_1873_);
                        crate::leanh::lean_dec_ref(v___x_1852_);
                        crate::leanh::lean_dec_ref(v___x_1851_);
                        crate::leanh::lean_dec_ref(v___x_1850_);
                        crate::leanh::lean_dec(v_tk_1847_);
                        v_a_1932_ = crate::leanh::lean_ctor_get(v___x_1905_, 0);
                        v_isSharedCheck_1939_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1905_)) as u8;
                        if v_isSharedCheck_1939_ == 0 {
                            v___x_1934_ = v___x_1905_;
                            v_isShared_1935_ = v_isSharedCheck_1939_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1932_);
                            crate::leanh::lean_dec(v___x_1905_);
                            v___x_1934_ = crate::leanh::lean_box(0);
                            v_isShared_1935_ = v_isSharedCheck_1939_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_result_1888_);
                    crate::leanh::lean_dec(v_a_1873_);
                    crate::leanh::lean_dec_ref(v___x_1852_);
                    crate::leanh::lean_dec_ref(v___x_1851_);
                    crate::leanh::lean_dec_ref(v___x_1850_);
                    crate::leanh::lean_dec(v_tk_1847_);
                    crate::leanh::lean_dec(v_a_1843_);
                    v_a_1940_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                    v_isSharedCheck_1947_ = (!crate::leanh::lean_is_exclusive(v___x_1900_)) as u8;
                    if v_isSharedCheck_1947_ == 0 {
                        v___x_1942_ = v___x_1900_;
                        v_isShared_1943_ = v_isSharedCheck_1947_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1940_);
                        crate::leanh::lean_dec(v___x_1900_);
                        v___x_1942_ = crate::leanh::lean_box(0);
                        v_isShared_1943_ = v_isSharedCheck_1947_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1935_ == 0 {
                    v___x_1937_ = v___x_1934_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1938_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
                    v___x_1937_ = v_reuseFailAlloc_1938_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1937_;
            }
            6 => {
                if v_isShared_1943_ == 0 {
                    v___x_1945_ = v___x_1942_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
                    v___x_1945_ = v_reuseFailAlloc_1946_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1945_;
            }
            8 => {
                if v_isShared_1955_ == 0 {
                    v___x_1957_ = v___x_1954_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
                    v___x_1957_ = v_reuseFailAlloc_1958_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1957_;
            }
            10 => {
                if v_isShared_1968_ == 0 {
                    v___x_1970_ = v___x_1967_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
                    v___x_1970_ = v_reuseFailAlloc_1971_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1970_;
            }
            12 => {
                if v_isShared_1976_ == 0 {
                    v___x_1978_ = v___x_1975_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
                    v___x_1978_ = v_reuseFailAlloc_1979_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1978_;
            }
            14 => {
                if v_isShared_1984_ == 0 {
                    v___x_1986_ = v___x_1983_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
                    v___x_1986_ = v_reuseFailAlloc_1987_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1989_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_1990_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___y_1991_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1992_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_tk_1993_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_1994_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_1995_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_1996_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_1997_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_1998_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1999_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2000_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2001_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2002_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2003_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2004_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2005_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2006_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2007_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_26742__boxed_2008_: u8 = 0;
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_26742__boxed_2008_ = (crate::leanh::lean_unbox(v___x_1992_) as u8);
    v_res_2009_ = l_Lean_Elab_Rewrites_evalExact___lam__3(
        v_a_1989_,
        v_a_1990_,
        v___y_1991_,
        v___x_26742__boxed_2008_,
        v_tk_1993_,
        v___x_1994_,
        v___x_1995_,
        v___x_1996_,
        v___x_1997_,
        v___x_1998_,
        v___y_1999_,
        v___y_2000_,
        v___y_2001_,
        v___y_2002_,
        v___y_2003_,
        v___y_2004_,
        v___y_2005_,
        v___y_2006_,
    );
    crate::leanh::lean_dec(v___y_2006_);
    crate::leanh::lean_dec_ref(v___y_2005_);
    crate::leanh::lean_dec(v___y_2004_);
    crate::leanh::lean_dec_ref(v___y_2003_);
    crate::leanh::lean_dec(v___y_2002_);
    crate::leanh::lean_dec_ref(v___y_2001_);
    crate::leanh::lean_dec(v___y_2000_);
    crate::leanh::lean_dec_ref(v___y_1999_);
    crate::leanh::lean_dec(v___x_1994_);
    crate::leanh::lean_dec(v___y_1991_);
    return v_res_2009_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(
    mut v_sz_2010_: usize,
    mut v_i_2011_: usize,
    mut v_bs_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2013_: u8 = 0;
    let mut v_v_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: usize = 0;
    let mut v___x_2019_: usize = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2013_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
                if v___x_2013_ == 0 {
                    return v_bs_2012_;
                } else {
                    v_v_2014_ = lean_array_uget(v_bs_2012_, v_i_2011_);
                    v___x_2015_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2016_ = lean_array_uset(v_bs_2012_, v_i_2011_, v___x_2015_);
                    v___x_2017_ = l_Lean_Syntax_getId(v_v_2014_);
                    crate::leanh::lean_dec(v_v_2014_);
                    v___x_2018_ = 1usize;
                    v___x_2019_ = lean_usize_add(v_i_2011_, v___x_2018_);
                    v___x_2020_ = lean_array_uset(v_bs_x27_2016_, v_i_2011_, v___x_2017_);
                    v_i_2011_ = v___x_2019_;
                    v_bs_2012_ = v___x_2020_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(
    mut v_sz_2022_: *mut crate::leanh::LeanObject,
    mut v_i_2023_: *mut crate::leanh::LeanObject,
    mut v_bs_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2025_: usize = 0;
    let mut v_i_boxed_2026_: usize = 0;
    let mut v_res_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2025_ = crate::leanh::lean_unbox_usize(v_sz_2022_);
    crate::leanh::lean_dec(v_sz_2022_);
    v_i_boxed_2026_ = crate::leanh::lean_unbox_usize(v_i_2023_);
    crate::leanh::lean_dec(v_i_2023_);
    v_res_2027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_boxed_2025_, v_i_boxed_2026_, v_bs_2024_);
    return v_res_2027_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(
    mut v___x_2028_: u8,
    mut v___x_2029_: u8,
    mut v_as_2030_: *mut crate::leanh::LeanObject,
    mut v_i_2031_: usize,
    mut v_stop_2032_: usize,
    mut v_b_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2039_: u8 = 0;
    let mut v_fst_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    let mut v_snd_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_unused_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2055_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2062_: u8 = 0;
    let mut v_unused_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2039_ = lean_usize_dec_eq(v_i_2031_, v_stop_2032_);
                if v___x_2039_ == 0 {
                    v_fst_2040_ = crate::leanh::lean_ctor_get(v_b_2033_, 0);
                    v___x_2041_ = (crate::leanh::lean_unbox(v_fst_2040_) as u8);
                    if v___x_2041_ == 0 {
                        v_snd_2042_ = crate::leanh::lean_ctor_get(v_b_2033_, 1);
                        v_isSharedCheck_2050_ = (!crate::leanh::lean_is_exclusive(v_b_2033_)) as u8;
                        if v_isSharedCheck_2050_ == 0 {
                            v_unused_2051_ = crate::leanh::lean_ctor_get(v_b_2033_, 0);
                            crate::leanh::lean_dec(v_unused_2051_);
                            v___x_2044_ = v_b_2033_;
                            v_isShared_2045_ = v_isSharedCheck_2050_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_2042_);
                            crate::leanh::lean_dec(v_b_2033_);
                            v___x_2044_ = crate::leanh::lean_box(0);
                            v_isShared_2045_ = v_isSharedCheck_2050_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_2052_ = crate::leanh::lean_ctor_get(v_b_2033_, 1);
                        v_isSharedCheck_2062_ = (!crate::leanh::lean_is_exclusive(v_b_2033_)) as u8;
                        if v_isSharedCheck_2062_ == 0 {
                            v_unused_2063_ = crate::leanh::lean_ctor_get(v_b_2033_, 0);
                            crate::leanh::lean_dec(v_unused_2063_);
                            v___x_2054_ = v_b_2033_;
                            v_isShared_2055_ = v_isSharedCheck_2062_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_2052_);
                            crate::leanh::lean_dec(v_b_2033_);
                            v___x_2054_ = crate::leanh::lean_box(0);
                            v_isShared_2055_ = v_isSharedCheck_2062_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_2033_;
                }
            }
            1 => {
                v___x_2036_ = 1usize;
                v___x_2037_ = lean_usize_add(v_i_2031_, v___x_2036_);
                v_i_2031_ = v___x_2037_;
                v_b_2033_ = v___y_2035_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2046_ = crate::leanh::lean_box((v___x_2028_) as usize);
                if v_isShared_2045_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2044_, 0, v___x_2046_);
                    v___x_2048_ = v___x_2044_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_snd_2042_);
                    v___x_2048_ = v_reuseFailAlloc_2049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_2035_ = v___x_2048_;
                state = 1;
                continue;
            }
            4 => {
                v___x_2056_ = lean_array_uget_borrowed(v_as_2030_, v_i_2031_);
                crate::leanh::lean_inc(v___x_2056_);
                v___x_2057_ = lean_array_push(v_snd_2052_, v___x_2056_);
                v___x_2058_ = crate::leanh::lean_box((v___x_2029_) as usize);
                if v_isShared_2055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2054_, 1, v___x_2057_);
                    crate::leanh::lean_ctor_set(v___x_2054_, 0, v___x_2058_);
                    v___x_2060_ = v___x_2054_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2061_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2057_);
                    v___x_2060_ = v_reuseFailAlloc_2061_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2035_ = v___x_2060_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(
    mut v___x_2064_: *mut crate::leanh::LeanObject,
    mut v___x_2065_: *mut crate::leanh::LeanObject,
    mut v_as_2066_: *mut crate::leanh::LeanObject,
    mut v_i_2067_: *mut crate::leanh::LeanObject,
    mut v_stop_2068_: *mut crate::leanh::LeanObject,
    mut v_b_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_27061__boxed_2070_: u8 = 0;
    let mut v___x_27062__boxed_2071_: u8 = 0;
    let mut v_i_boxed_2072_: usize = 0;
    let mut v_stop_boxed_2073_: usize = 0;
    let mut v_res_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_27061__boxed_2070_ = (crate::leanh::lean_unbox(v___x_2064_) as u8);
    v___x_27062__boxed_2071_ = (crate::leanh::lean_unbox(v___x_2065_) as u8);
    v_i_boxed_2072_ = crate::leanh::lean_unbox_usize(v_i_2067_);
    crate::leanh::lean_dec(v_i_2067_);
    v_stop_boxed_2073_ = crate::leanh::lean_unbox_usize(v_stop_2068_);
    crate::leanh::lean_dec(v_stop_2068_);
    v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_27061__boxed_2070_, v___x_27062__boxed_2071_, v_as_2066_, v_i_boxed_2072_, v_stop_boxed_2073_, v_b_2069_);
    crate::leanh::lean_dec_ref(v_as_2066_);
    return v_res_2074_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(
    mut v_as_2075_: *mut crate::leanh::LeanObject,
    mut v_i_2076_: usize,
    mut v_stop_2077_: usize,
    mut v_b_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: usize = 0;
    let mut v___x_2083_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2079_ = lean_usize_dec_eq(v_i_2076_, v_stop_2077_);
                if v___x_2079_ == 0 {
                    v___x_2080_ = lean_array_uget_borrowed(v_as_2075_, v_i_2076_);
                    crate::leanh::lean_inc(v___x_2080_);
                    v___x_2081_ = l_Lean_NameSet_insert(v_b_2078_, v___x_2080_);
                    v___x_2082_ = 1usize;
                    v___x_2083_ = lean_usize_add(v_i_2076_, v___x_2082_);
                    v_i_2076_ = v___x_2083_;
                    v_b_2078_ = v___x_2081_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2078_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(
    mut v_as_2085_: *mut crate::leanh::LeanObject,
    mut v_i_2086_: *mut crate::leanh::LeanObject,
    mut v_stop_2087_: *mut crate::leanh::LeanObject,
    mut v_b_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2089_: usize = 0;
    let mut v_stop_boxed_2090_: usize = 0;
    let mut v_res_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2089_ = crate::leanh::lean_unbox_usize(v_i_2086_);
    crate::leanh::lean_dec(v_i_2086_);
    v_stop_boxed_2090_ = crate::leanh::lean_unbox_usize(v_stop_2087_);
    crate::leanh::lean_dec(v_stop_2087_);
    v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_as_2085_, v_i_boxed_2089_, v_stop_boxed_2090_, v_b_2088_);
    crate::leanh::lean_dec_ref(v_as_2085_);
    return v_res_2091_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(
    mut v_sz_2095_: usize,
    mut v_i_2096_: usize,
    mut v_bs_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbidden_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: usize = 0;
    let mut v___x_2109_: usize = 0;
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2098_ = lean_usize_dec_lt(v_i_2096_, v_sz_2095_);
                if v___x_2098_ == 0 {
                    v___x_2099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2099_, 0, v_bs_2097_);
                    return v___x_2099_;
                } else {
                    v_v_2100_ = lean_array_uget(v_bs_2097_, v_i_2096_);
                    v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1;
                    crate::leanh::lean_inc(v_v_2100_);
                    v___x_2102_ = l_Lean_Syntax_isOfKind(v_v_2100_, v___x_2101_);
                    if v___x_2102_ == 0 {
                        crate::leanh::lean_dec(v_v_2100_);
                        crate::leanh::lean_dec_ref(v_bs_2097_);
                        v___x_2103_ = crate::leanh::lean_box(0);
                        return v___x_2103_;
                    } else {
                        v___x_2104_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2105_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2106_ = lean_array_uset(v_bs_2097_, v_i_2096_, v___x_2105_);
                        v_forbidden_2107_ = l_Lean_Syntax_getArg(v_v_2100_, v___x_2104_);
                        crate::leanh::lean_dec(v_v_2100_);
                        v___x_2108_ = 1usize;
                        v___x_2109_ = lean_usize_add(v_i_2096_, v___x_2108_);
                        v___x_2110_ = lean_array_uset(v_bs_x27_2106_, v_i_2096_, v_forbidden_2107_);
                        v_i_2096_ = v___x_2109_;
                        v_bs_2097_ = v___x_2110_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(
    mut v_sz_2112_: *mut crate::leanh::LeanObject,
    mut v_i_2113_: *mut crate::leanh::LeanObject,
    mut v_bs_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2115_: usize = 0;
    let mut v_i_boxed_2116_: usize = 0;
    let mut v_res_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2115_ = crate::leanh::lean_unbox_usize(v_sz_2112_);
    crate::leanh::lean_dec(v_sz_2112_);
    v_i_boxed_2116_ = crate::leanh::lean_unbox_usize(v_i_2113_);
    crate::leanh::lean_dec(v_i_2113_);
    v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_boxed_2115_, v_i_boxed_2116_, v_bs_2114_);
    return v_res_2117_;
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact(
    mut v_stx_2141_: *mut crate::leanh::LeanObject,
    mut v_a_2142_: *mut crate::leanh::LeanObject,
    mut v_a_2143_: *mut crate::leanh::LeanObject,
    mut v_a_2144_: *mut crate::leanh::LeanObject,
    mut v_a_2145_: *mut crate::leanh::LeanObject,
    mut v_a_2146_: *mut crate::leanh::LeanObject,
    mut v_a_2147_: *mut crate::leanh::LeanObject,
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2205_: u8 = 0;
    let mut v_a_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2209_: u8 = 0;
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut v___y_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2228_: usize = 0;
    let mut v___x_2229_: usize = 0;
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: u8 = 0;
    let mut v___x_2234_: usize = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: usize = 0;
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbidden_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v___y_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2273_: usize = 0;
    let mut v___x_2274_: usize = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: u8 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: usize = 0;
    let mut v___x_2306_: usize = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: usize = 0;
    let mut v___x_2310_: usize = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: u8 = 0;
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2167_ = l_Lean_Elab_Rewrites_evalExact___closed__0;
                v___x_2168_ = l_Lean_Elab_Rewrites_evalExact___closed__1;
                v___x_2169_ = l_Lean_Elab_Rewrites_evalExact___closed__2;
                v___x_2170_ = l_Lean_Elab_Rewrites_evalExact___closed__4;
                crate::leanh::lean_inc(v_stx_2141_);
                v___x_2171_ = l_Lean_Syntax_isOfKind(v_stx_2141_, v___x_2170_);
                if v___x_2171_ == 0 {
                    crate::leanh::lean_dec(v_stx_2141_);
                    v___x_2172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
                    return v___x_2172_;
                } else {
                    v___f_2173_ = l_Lean_Elab_Rewrites_evalExact___closed__5;
                    v___x_2174_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_2175_ = l_Lean_Syntax_getArg(v_stx_2141_, v___x_2174_);
                    v___x_2277_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2314_ = l_Lean_Syntax_getArg(v_stx_2141_, v___x_2277_);
                    v___x_2315_ = l_Lean_Syntax_isNone(v___x_2314_);
                    if v___x_2315_ == 0 {
                        crate::leanh::lean_inc(v___x_2314_);
                        v___x_2316_ = l_Lean_Syntax_matchesNull(v___x_2314_, v___x_2277_);
                        if v___x_2316_ == 0 {
                            crate::leanh::lean_dec(v___x_2314_);
                            crate::leanh::lean_dec(v_tk_2175_);
                            crate::leanh::lean_dec(v_stx_2141_);
                            v___x_2317_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
                            return v___x_2317_;
                        } else {
                            v_loc_2318_ = l_Lean_Syntax_getArg(v___x_2314_, v___x_2174_);
                            crate::leanh::lean_dec(v___x_2314_);
                            v___x_2319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2319_, 0, v_loc_2318_);
                            v_loc_2279_ = v___x_2319_;
                            v___y_2280_ = v_a_2142_;
                            v___y_2281_ = v_a_2143_;
                            v___y_2282_ = v_a_2144_;
                            v___y_2283_ = v_a_2145_;
                            v___y_2284_ = v_a_2146_;
                            v___y_2285_ = v_a_2147_;
                            v___y_2286_ = v_a_2148_;
                            v___y_2287_ = v_a_2149_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2314_);
                        v___x_2320_ = crate::leanh::lean_box(0);
                        v_loc_2279_ = v___x_2320_;
                        v___y_2280_ = v_a_2142_;
                        v___y_2281_ = v_a_2143_;
                        v___y_2282_ = v_a_2144_;
                        v___y_2283_ = v_a_2145_;
                        v___y_2284_ = v_a_2146_;
                        v___y_2285_ = v_a_2147_;
                        v___y_2286_ = v_a_2148_;
                        v___y_2287_ = v_a_2149_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2164_ = l_Lean_mkOptionalNode(v___y_2163_);
                v___x_2165_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2164_);
                crate::leanh::lean_dec(v___x_2164_);
                crate::leanh::lean_inc_ref(v___y_2152_);
                v___x_2166_ = l_Lean_Elab_Tactic_withLocation(
                    v___x_2165_,
                    v___y_2156_,
                    v___y_2155_,
                    v___y_2152_,
                    v___y_2159_,
                    v___y_2162_,
                    v___y_2158_,
                    v___y_2154_,
                    v___y_2153_,
                    v___y_2157_,
                    v___y_2161_,
                    v___y_2160_,
                );
                crate::leanh::lean_dec(v___x_2165_);
                return v___x_2166_;
            }
            2 => {
                v___x_2189_ = l_Lean_Elab_Rewrites_evalExact___closed__7;
                v___x_2190_ = crate::leanh::lean_unsigned_to_nat(90);
                v___x_2191_ = l_Lean_reportOutOfHeartbeats(
                    v___x_2189_,
                    v_tk_2175_,
                    v___x_2190_,
                    v___y_2186_,
                    v___y_2185_,
                );
                if crate::leanh::lean_obj_tag(v___x_2191_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2191_, 1);
                    v___x_2192_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_2187_,
                        v___y_2180_,
                        v___y_2181_,
                        v___y_2186_,
                        v___y_2185_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2192_) == 0 {
                        v_a_2193_ = crate::leanh::lean_ctor_get(v___x_2192_, 0);
                        crate::leanh::lean_inc_n(v_a_2193_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2192_, 1);
                        crate::leanh::lean_inc(v_tk_2175_);
                        crate::leanh::lean_inc(v___y_2188_);
                        crate::leanh::lean_inc(v___y_2177_);
                        v___f_2194_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Rewrites_evalExact___lam__2___boxed
                                as *mut core::ffi::c_void,
                            16,
                            6,
                        );
                        crate::leanh::lean_closure_set(v___f_2194_, 0, v___y_2177_);
                        crate::leanh::lean_closure_set(v___f_2194_, 1, v_a_2193_);
                        crate::leanh::lean_closure_set(v___f_2194_, 2, v___y_2188_);
                        crate::leanh::lean_closure_set(v___f_2194_, 3, v_tk_2175_);
                        crate::leanh::lean_closure_set(v___f_2194_, 4, v___x_2190_);
                        crate::leanh::lean_closure_set(v___f_2194_, 5, v___x_2174_);
                        v___x_2195_ = crate::leanh::lean_box((v___x_2171_) as usize);
                        v___f_2196_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Rewrites_evalExact___lam__3___boxed
                                as *mut core::ffi::c_void,
                            19,
                            10,
                        );
                        crate::leanh::lean_closure_set(v___f_2196_, 0, v_a_2193_);
                        crate::leanh::lean_closure_set(v___f_2196_, 1, v___y_2177_);
                        crate::leanh::lean_closure_set(v___f_2196_, 2, v___y_2188_);
                        crate::leanh::lean_closure_set(v___f_2196_, 3, v___x_2195_);
                        crate::leanh::lean_closure_set(v___f_2196_, 4, v_tk_2175_);
                        crate::leanh::lean_closure_set(v___f_2196_, 5, v___x_2190_);
                        crate::leanh::lean_closure_set(v___f_2196_, 6, v___x_2174_);
                        crate::leanh::lean_closure_set(v___f_2196_, 7, v___x_2167_);
                        crate::leanh::lean_closure_set(v___f_2196_, 8, v___x_2168_);
                        crate::leanh::lean_closure_set(v___f_2196_, 9, v___x_2169_);
                        if crate::leanh::lean_obj_tag(v___y_2182_) == 0 {
                            v___x_2197_ = crate::leanh::lean_box(0);
                            v___y_2152_ = v___y_2178_;
                            v___y_2153_ = v___y_2180_;
                            v___y_2154_ = v___y_2179_;
                            v___y_2155_ = v___f_2196_;
                            v___y_2156_ = v___f_2194_;
                            v___y_2157_ = v___y_2181_;
                            v___y_2158_ = v___y_2183_;
                            v___y_2159_ = v___y_2184_;
                            v___y_2160_ = v___y_2185_;
                            v___y_2161_ = v___y_2186_;
                            v___y_2162_ = v___y_2187_;
                            v___y_2163_ = v___x_2197_;
                            state = 1;
                            continue;
                        } else {
                            v_val_2198_ = crate::leanh::lean_ctor_get(v___y_2182_, 0);
                            v_isSharedCheck_2205_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2182_)) as u8;
                            if v_isSharedCheck_2205_ == 0 {
                                v___x_2200_ = v___y_2182_;
                                v_isShared_2201_ = v_isSharedCheck_2205_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2198_);
                                crate::leanh::lean_dec(v___y_2182_);
                                v___x_2200_ = crate::leanh::lean_box(0);
                                v_isShared_2201_ = v_isSharedCheck_2205_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2188_);
                        crate::leanh::lean_dec(v___y_2182_);
                        crate::leanh::lean_dec(v___y_2177_);
                        crate::leanh::lean_dec(v_tk_2175_);
                        v_a_2206_ = crate::leanh::lean_ctor_get(v___x_2192_, 0);
                        v_isSharedCheck_2213_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2192_)) as u8;
                        if v_isSharedCheck_2213_ == 0 {
                            v___x_2208_ = v___x_2192_;
                            v_isShared_2209_ = v_isSharedCheck_2213_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2206_);
                            crate::leanh::lean_dec(v___x_2192_);
                            v___x_2208_ = crate::leanh::lean_box(0);
                            v_isShared_2209_ = v_isSharedCheck_2213_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2188_);
                    crate::leanh::lean_dec(v___y_2182_);
                    crate::leanh::lean_dec(v___y_2177_);
                    crate::leanh::lean_dec(v_tk_2175_);
                    return v___x_2191_;
                }
            }
            3 => {
                if v_isShared_2201_ == 0 {
                    v___x_2203_ = v___x_2200_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_val_2198_);
                    v___x_2203_ = v_reuseFailAlloc_2204_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2152_ = v___y_2178_;
                v___y_2153_ = v___y_2180_;
                v___y_2154_ = v___y_2179_;
                v___y_2155_ = v___f_2196_;
                v___y_2156_ = v___f_2194_;
                v___y_2157_ = v___y_2181_;
                v___y_2158_ = v___y_2183_;
                v___y_2159_ = v___y_2184_;
                v___y_2160_ = v___y_2185_;
                v___y_2161_ = v___y_2186_;
                v___y_2162_ = v___y_2187_;
                v___y_2163_ = v___x_2203_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_2209_ == 0 {
                    v___x_2211_ = v___x_2208_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
                    v___x_2211_ = v_reuseFailAlloc_2212_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2211_;
            }
            7 => {
                v_sz_2228_ = lean_array_size(v___y_2227_);
                v___x_2229_ = 0usize;
                v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_2228_, v___x_2229_, v___y_2227_);
                v___x_2231_ = lean_array_get_size(v___x_2230_);
                v___x_2232_ = lean_nat_dec_lt(v___x_2174_, v___x_2231_);
                if v___x_2232_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2230_);
                    crate::leanh::lean_inc(v___y_2217_);
                    v___y_2177_ = v___y_2215_;
                    v___y_2178_ = v___y_2216_;
                    v___y_2179_ = v___y_2219_;
                    v___y_2180_ = v___y_2218_;
                    v___y_2181_ = v___y_2220_;
                    v___y_2182_ = v___y_2221_;
                    v___y_2183_ = v___y_2222_;
                    v___y_2184_ = v___y_2223_;
                    v___y_2185_ = v___y_2225_;
                    v___y_2186_ = v___y_2224_;
                    v___y_2187_ = v___y_2226_;
                    v___y_2188_ = v___y_2217_;
                    state = 2;
                    continue;
                } else {
                    v___x_2233_ = lean_nat_dec_le(v___x_2231_, v___x_2231_);
                    if v___x_2233_ == 0 {
                        if v___x_2232_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2230_);
                            crate::leanh::lean_inc(v___y_2217_);
                            v___y_2177_ = v___y_2215_;
                            v___y_2178_ = v___y_2216_;
                            v___y_2179_ = v___y_2219_;
                            v___y_2180_ = v___y_2218_;
                            v___y_2181_ = v___y_2220_;
                            v___y_2182_ = v___y_2221_;
                            v___y_2183_ = v___y_2222_;
                            v___y_2184_ = v___y_2223_;
                            v___y_2185_ = v___y_2225_;
                            v___y_2186_ = v___y_2224_;
                            v___y_2187_ = v___y_2226_;
                            v___y_2188_ = v___y_2217_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2234_ = lean_usize_of_nat(v___x_2231_);
                            crate::leanh::lean_inc(v___y_2217_);
                            v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_2230_, v___x_2229_, v___x_2234_, v___y_2217_);
                            crate::leanh::lean_dec_ref(v___x_2230_);
                            v___y_2177_ = v___y_2215_;
                            v___y_2178_ = v___y_2216_;
                            v___y_2179_ = v___y_2219_;
                            v___y_2180_ = v___y_2218_;
                            v___y_2181_ = v___y_2220_;
                            v___y_2182_ = v___y_2221_;
                            v___y_2183_ = v___y_2222_;
                            v___y_2184_ = v___y_2223_;
                            v___y_2185_ = v___y_2225_;
                            v___y_2186_ = v___y_2224_;
                            v___y_2187_ = v___y_2226_;
                            v___y_2188_ = v___x_2235_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2236_ = lean_usize_of_nat(v___x_2231_);
                        crate::leanh::lean_inc(v___y_2217_);
                        v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_2230_, v___x_2229_, v___x_2236_, v___y_2217_);
                        crate::leanh::lean_dec_ref(v___x_2230_);
                        v___y_2177_ = v___y_2215_;
                        v___y_2178_ = v___y_2216_;
                        v___y_2179_ = v___y_2219_;
                        v___y_2180_ = v___y_2218_;
                        v___y_2181_ = v___y_2220_;
                        v___y_2182_ = v___y_2221_;
                        v___y_2183_ = v___y_2222_;
                        v___y_2184_ = v___y_2223_;
                        v___y_2185_ = v___y_2225_;
                        v___y_2186_ = v___y_2224_;
                        v___y_2187_ = v___y_2226_;
                        v___y_2188_ = v___x_2237_;
                        state = 2;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2249_ = l_Lean_Meta_Rewrites_createModuleTreeRef(
                    v___y_2245_,
                    v___y_2246_,
                    v___y_2247_,
                    v___y_2248_,
                );
                if crate::leanh::lean_obj_tag(v___x_2249_) == 0 {
                    v_a_2250_ = crate::leanh::lean_ctor_get(v___x_2249_, 0);
                    crate::leanh::lean_inc(v_a_2250_);
                    crate::leanh::lean_dec_ref_known(v___x_2249_, 1);
                    v___x_2251_ = l_Lean_NameSet_empty;
                    if crate::leanh::lean_obj_tag(v_forbidden_2240_) == 0 {
                        v___x_2252_ = l_Lean_Elab_Rewrites_evalExact___closed__8;
                        v___y_2215_ = v_a_2250_;
                        v___y_2216_ = v___f_2173_;
                        v___y_2217_ = v___x_2251_;
                        v___y_2218_ = v___y_2245_;
                        v___y_2219_ = v___y_2244_;
                        v___y_2220_ = v___y_2246_;
                        v___y_2221_ = v___y_2239_;
                        v___y_2222_ = v___y_2243_;
                        v___y_2223_ = v___y_2241_;
                        v___y_2224_ = v___y_2247_;
                        v___y_2225_ = v___y_2248_;
                        v___y_2226_ = v___y_2242_;
                        v___y_2227_ = v___x_2252_;
                        state = 7;
                        continue;
                    } else {
                        v_val_2253_ = crate::leanh::lean_ctor_get(v_forbidden_2240_, 0);
                        crate::leanh::lean_inc(v_val_2253_);
                        crate::leanh::lean_dec_ref_known(v_forbidden_2240_, 1);
                        v___y_2215_ = v_a_2250_;
                        v___y_2216_ = v___f_2173_;
                        v___y_2217_ = v___x_2251_;
                        v___y_2218_ = v___y_2245_;
                        v___y_2219_ = v___y_2244_;
                        v___y_2220_ = v___y_2246_;
                        v___y_2221_ = v___y_2239_;
                        v___y_2222_ = v___y_2243_;
                        v___y_2223_ = v___y_2241_;
                        v___y_2224_ = v___y_2247_;
                        v___y_2225_ = v___y_2248_;
                        v___y_2226_ = v___y_2242_;
                        v___y_2227_ = v_val_2253_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_forbidden_2240_);
                    crate::leanh::lean_dec(v___y_2239_);
                    crate::leanh::lean_dec(v_tk_2175_);
                    v_a_2254_ = crate::leanh::lean_ctor_get(v___x_2249_, 0);
                    v_isSharedCheck_2261_ = (!crate::leanh::lean_is_exclusive(v___x_2249_)) as u8;
                    if v_isSharedCheck_2261_ == 0 {
                        v___x_2256_ = v___x_2249_;
                        v_isShared_2257_ = v_isSharedCheck_2261_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2254_);
                        crate::leanh::lean_dec(v___x_2249_);
                        v___x_2256_ = crate::leanh::lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2261_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2257_ == 0 {
                    v___x_2259_ = v___x_2256_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
                    v___x_2259_ = v_reuseFailAlloc_2260_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2259_;
            }
            11 => {
                v_sz_2273_ = lean_array_size(v___y_2272_);
                v___x_2274_ = 0usize;
                v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_2273_, v___x_2274_, v___y_2272_);
                if crate::leanh::lean_obj_tag(v___x_2275_) == 0 {
                    crate::leanh::lean_dec(v___y_2266_);
                    crate::leanh::lean_dec(v_tk_2175_);
                    v___x_2276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
                    return v___x_2276_;
                } else {
                    v___y_2239_ = v___y_2266_;
                    v_forbidden_2240_ = v___x_2275_;
                    v___y_2241_ = v___y_2269_;
                    v___y_2242_ = v___y_2271_;
                    v___y_2243_ = v___y_2265_;
                    v___y_2244_ = v___y_2264_;
                    v___y_2245_ = v___y_2267_;
                    v___y_2246_ = v___y_2270_;
                    v___y_2247_ = v___y_2263_;
                    v___y_2248_ = v___y_2268_;
                    state = 8;
                    continue;
                }
            }
            12 => {
                v___x_2288_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2289_ = l_Lean_Syntax_getArg(v_stx_2141_, v___x_2288_);
                crate::leanh::lean_dec(v_stx_2141_);
                v___x_2290_ = l_Lean_Syntax_isNone(v___x_2289_);
                if v___x_2290_ == 0 {
                    crate::leanh::lean_inc(v___x_2289_);
                    v___x_2291_ = l_Lean_Syntax_matchesNull(v___x_2289_, v___x_2277_);
                    if v___x_2291_ == 0 {
                        crate::leanh::lean_dec(v___x_2289_);
                        crate::leanh::lean_dec(v_loc_2279_);
                        crate::leanh::lean_dec(v_tk_2175_);
                        v___x_2292_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
                        return v___x_2292_;
                    } else {
                        v___x_2293_ = l_Lean_Syntax_getArg(v___x_2289_, v___x_2174_);
                        crate::leanh::lean_dec(v___x_2289_);
                        v___x_2294_ = l_Lean_Elab_Rewrites_evalExact___closed__10;
                        crate::leanh::lean_inc(v___x_2293_);
                        v___x_2295_ = l_Lean_Syntax_isOfKind(v___x_2293_, v___x_2294_);
                        if v___x_2295_ == 0 {
                            crate::leanh::lean_dec(v___x_2293_);
                            crate::leanh::lean_dec(v_loc_2279_);
                            crate::leanh::lean_dec(v_tk_2175_);
                            v___x_2296_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
                            return v___x_2296_;
                        } else {
                            v___x_2297_ = l_Lean_Syntax_getArg(v___x_2293_, v___x_2277_);
                            crate::leanh::lean_dec(v___x_2293_);
                            v___x_2298_ = l_Lean_Syntax_getArgs(v___x_2297_);
                            crate::leanh::lean_dec(v___x_2297_);
                            v___x_2299_ = l_Lean_Elab_Rewrites_evalExact___closed__11;
                            v___x_2300_ = lean_array_get_size(v___x_2298_);
                            v___x_2301_ = lean_nat_dec_lt(v___x_2174_, v___x_2300_);
                            if v___x_2301_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2298_);
                                v___y_2263_ = v___y_2286_;
                                v___y_2264_ = v___y_2283_;
                                v___y_2265_ = v___y_2282_;
                                v___y_2266_ = v_loc_2279_;
                                v___y_2267_ = v___y_2284_;
                                v___y_2268_ = v___y_2287_;
                                v___y_2269_ = v___y_2280_;
                                v___y_2270_ = v___y_2285_;
                                v___y_2271_ = v___y_2281_;
                                v___y_2272_ = v___x_2299_;
                                state = 11;
                                continue;
                            } else {
                                v___x_2302_ = crate::leanh::lean_box((v___x_2295_) as usize);
                                v___x_2303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2302_);
                                crate::leanh::lean_ctor_set(v___x_2303_, 1, v___x_2299_);
                                v___x_2304_ = lean_nat_dec_le(v___x_2300_, v___x_2300_);
                                if v___x_2304_ == 0 {
                                    if v___x_2301_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_2303_, 2);
                                        crate::leanh::lean_dec_ref(v___x_2298_);
                                        v___y_2263_ = v___y_2286_;
                                        v___y_2264_ = v___y_2283_;
                                        v___y_2265_ = v___y_2282_;
                                        v___y_2266_ = v_loc_2279_;
                                        v___y_2267_ = v___y_2284_;
                                        v___y_2268_ = v___y_2287_;
                                        v___y_2269_ = v___y_2280_;
                                        v___y_2270_ = v___y_2285_;
                                        v___y_2271_ = v___y_2281_;
                                        v___y_2272_ = v___x_2299_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v___x_2305_ = 0usize;
                                        v___x_2306_ = lean_usize_of_nat(v___x_2300_);
                                        v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_2295_, v___x_2290_, v___x_2298_, v___x_2305_, v___x_2306_, v___x_2303_);
                                        crate::leanh::lean_dec_ref(v___x_2298_);
                                        v_snd_2308_ = crate::leanh::lean_ctor_get(v___x_2307_, 1);
                                        crate::leanh::lean_inc(v_snd_2308_);
                                        crate::leanh::lean_dec_ref(v___x_2307_);
                                        v___y_2263_ = v___y_2286_;
                                        v___y_2264_ = v___y_2283_;
                                        v___y_2265_ = v___y_2282_;
                                        v___y_2266_ = v_loc_2279_;
                                        v___y_2267_ = v___y_2284_;
                                        v___y_2268_ = v___y_2287_;
                                        v___y_2269_ = v___y_2280_;
                                        v___y_2270_ = v___y_2285_;
                                        v___y_2271_ = v___y_2281_;
                                        v___y_2272_ = v_snd_2308_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    v___x_2309_ = 0usize;
                                    v___x_2310_ = lean_usize_of_nat(v___x_2300_);
                                    v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_2295_, v___x_2290_, v___x_2298_, v___x_2309_, v___x_2310_, v___x_2303_);
                                    crate::leanh::lean_dec_ref(v___x_2298_);
                                    v_snd_2312_ = crate::leanh::lean_ctor_get(v___x_2311_, 1);
                                    crate::leanh::lean_inc(v_snd_2312_);
                                    crate::leanh::lean_dec_ref(v___x_2311_);
                                    v___y_2263_ = v___y_2286_;
                                    v___y_2264_ = v___y_2283_;
                                    v___y_2265_ = v___y_2282_;
                                    v___y_2266_ = v_loc_2279_;
                                    v___y_2267_ = v___y_2284_;
                                    v___y_2268_ = v___y_2287_;
                                    v___y_2269_ = v___y_2280_;
                                    v___y_2270_ = v___y_2285_;
                                    v___y_2271_ = v___y_2281_;
                                    v___y_2272_ = v_snd_2312_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2289_);
                    v___x_2313_ = crate::leanh::lean_box(0);
                    v___y_2239_ = v_loc_2279_;
                    v_forbidden_2240_ = v___x_2313_;
                    v___y_2241_ = v___y_2280_;
                    v___y_2242_ = v___y_2281_;
                    v___y_2243_ = v___y_2282_;
                    v___y_2244_ = v___y_2283_;
                    v___y_2245_ = v___y_2284_;
                    v___y_2246_ = v___y_2285_;
                    v___y_2247_ = v___y_2286_;
                    v___y_2248_ = v___y_2287_;
                    state = 8;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Rewrites_evalExact___boxed(
    mut v_stx_2321_: *mut crate::leanh::LeanObject,
    mut v_a_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
    mut v_a_2325_: *mut crate::leanh::LeanObject,
    mut v_a_2326_: *mut crate::leanh::LeanObject,
    mut v_a_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Lean_Elab_Rewrites_evalExact(
        v_stx_2321_,
        v_a_2322_,
        v_a_2323_,
        v_a_2324_,
        v_a_2325_,
        v_a_2326_,
        v_a_2327_,
        v_a_2328_,
        v_a_2329_,
    );
    crate::leanh::lean_dec(v_a_2329_);
    crate::leanh::lean_dec_ref(v_a_2328_);
    crate::leanh::lean_dec(v_a_2327_);
    crate::leanh::lean_dec_ref(v_a_2326_);
    crate::leanh::lean_dec(v_a_2325_);
    crate::leanh::lean_dec_ref(v_a_2324_);
    crate::leanh::lean_dec(v_a_2323_);
    crate::leanh::lean_dec_ref(v_a_2322_);
    return v_res_2331_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(
    mut v_00_u03b1_2332_: *mut crate::leanh::LeanObject,
    mut v_msg_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2343_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(
        v_msg_2333_,
        v___y_2338_,
        v___y_2339_,
        v___y_2340_,
        v___y_2341_,
    );
    return v___x_2343_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(
    mut v_00_u03b1_2344_: *mut crate::leanh::LeanObject,
    mut v_msg_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
    mut v___y_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2355_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(
        v_00_u03b1_2344_,
        v_msg_2345_,
        v___y_2346_,
        v___y_2347_,
        v___y_2348_,
        v___y_2349_,
        v___y_2350_,
        v___y_2351_,
        v___y_2352_,
        v___y_2353_,
    );
    crate::leanh::lean_dec(v___y_2353_);
    crate::leanh::lean_dec_ref(v___y_2352_);
    crate::leanh::lean_dec(v___y_2351_);
    crate::leanh::lean_dec_ref(v___y_2350_);
    crate::leanh::lean_dec(v___y_2349_);
    crate::leanh::lean_dec_ref(v___y_2348_);
    crate::leanh::lean_dec(v___y_2347_);
    crate::leanh::lean_dec_ref(v___y_2346_);
    return v_res_2355_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(
    mut v_f_2356_: *mut crate::leanh::LeanObject,
    mut v_tk_2357_: *mut crate::leanh::LeanObject,
    mut v_as_2358_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2359_: *mut crate::leanh::LeanObject,
    mut v_b_2360_: *mut crate::leanh::LeanObject,
    mut v_a_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(
        v_f_2356_,
        v_tk_2357_,
        v_as_x27_2359_,
        v_b_2360_,
        v___y_2362_,
        v___y_2363_,
        v___y_2364_,
        v___y_2365_,
        v___y_2366_,
        v___y_2367_,
        v___y_2368_,
        v___y_2369_,
    );
    return v___x_2371_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(
    mut v_f_2372_: *mut crate::leanh::LeanObject,
    mut v_tk_2373_: *mut crate::leanh::LeanObject,
    mut v_as_2374_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2375_: *mut crate::leanh::LeanObject,
    mut v_b_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2387_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(
        v_f_2372_,
        v_tk_2373_,
        v_as_2374_,
        v_as_x27_2375_,
        v_b_2376_,
        v_a_2377_,
        v___y_2378_,
        v___y_2379_,
        v___y_2380_,
        v___y_2381_,
        v___y_2382_,
        v___y_2383_,
        v___y_2384_,
        v___y_2385_,
    );
    crate::leanh::lean_dec(v___y_2385_);
    crate::leanh::lean_dec_ref(v___y_2384_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v___y_2382_);
    crate::leanh::lean_dec(v___y_2381_);
    crate::leanh::lean_dec_ref(v___y_2380_);
    crate::leanh::lean_dec(v___y_2379_);
    crate::leanh::lean_dec_ref(v___y_2378_);
    crate::leanh::lean_dec(v_as_x27_2375_);
    crate::leanh::lean_dec(v_as_2374_);
    return v_res_2387_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2398_ = l_Lean_Elab_Rewrites_evalExact___closed__4;
    v___x_2399_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3;
    v___x_2400_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Rewrites_evalExact___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2401_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2397_,
        v___x_2398_,
        v___x_2399_,
        v___x_2400_,
    );
    return v___x_2401_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(
    mut v_a_2402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2403_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
    return v_res_2403_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3;
    v___x_2431_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6;
    v___x_2432_ = l_Lean_addBuiltinDeclarationRanges(v___x_2430_, v___x_2431_);
    return v___x_2432_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(
    mut v_a_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2434_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
    return v_res_2434_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Rewrites(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rewrites(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Rewrites(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Rewrites(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rewrites(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rewrites(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Rewrites(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Rewrites(builtin);
}
