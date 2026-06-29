// Lean compiler output
// Module: Lean.Meta.Native
// Imports: Lean.Meta.Basic Lean.Util.CollectLevelParams Lean.Elab.DeclarationRange Lean.Compiler.Options
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::AddDecl::{l_Lean_addAndCompile, l_Lean_addDecl};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_markMeta;
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_postponeCompile,
    l_Lean_Compiler_compiler_relaxedMetaCheck, runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_DeclNameGenerator_mkUniqueName, l_Lean_Elab_async, l_Lean_Exception_isRuntime,
    l_Lean_diagnostics,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_DeclarationRange_ofStringPositions;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_declRangeExt;
use crate::r#gen::Lean::Elab::DeclarationRange::{
    initialize_Lean_Elab_DeclarationRange, runtime_initialize_Lean_Elab_DeclarationRange,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::EnvExtension::l_Lean_MapDeclarationExtension_insert___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_evalConst___redArg, l_Lean_Environment_unlockAsync,
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_mkApp3, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_mkLevelParam};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
use crate::r#gen::Lean::Util::CollectLevelParams::{
    initialize_Lean_Util_CollectLevelParams, l_Lean_collectLevelParams,
    runtime_initialize_Lean_Util_CollectLevelParams,
};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::ffi::lean_mk_array;
use crate::ffi::lean_array_to_list;
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_has_compile_error;
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value: crate::leanh::LeanStringObject<57> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 57,
        m_capacity: 57,
        m_length: 56,
        m_data: [
            96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 67, 111, 117, 108, 100, 32, 110, 111, 116,
            32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 100, 101, 99, 105, 100, 97, 98, 108, 101,
            32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 32, 69, 114, 114, 111, 114, 58, 32, 0,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            96, 32, 102, 97, 105, 108, 101, 100, 46, 32, 69, 114, 114, 111, 114, 58, 32, 0,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value)
                as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__2_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_nativeEqTrue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__4_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [95, 110, 97, 116, 105, 118, 101, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__4_value)
                as *mut crate::leanh::LeanObject,
            12194354677470204327 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 101, 99, 108, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__6_value)
                as *mut crate::leanh::LeanObject,
            13787886431423481210 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__8_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [97, 120, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__8_value)
                as *mut crate::leanh::LeanObject,
            16160311484268338767 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__10_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__10_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__16_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value)
                as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_nativeEqTrue___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__16_value)
                as *mut crate::leanh::LeanObject,
            9255189395584251158 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__19_value: crate::leanh::LeanStringObject<63> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 63,
        m_capacity: 63,
        m_length: 62,
        m_data: [
            96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 67, 97, 110, 110, 111, 116, 32, 110, 97,
            116, 105, 118, 101, 32, 100, 101, 99, 105, 100, 101, 32, 112, 114, 111, 112, 111, 115,
            105, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 109, 101, 116, 97, 118, 97, 114,
            105, 97, 98, 108, 101, 115, 58, 0,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__21_value: crate::leanh::LeanStringObject<64> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 64,
        m_capacity: 64,
        m_length: 63,
        m_data: [
            96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 67, 97, 110, 110, 111, 116, 32, 110, 97,
            116, 105, 118, 101, 32, 100, 101, 99, 105, 100, 101, 32, 112, 114, 111, 112, 111, 115,
            105, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 102, 114, 101, 101, 32, 118, 97,
            114, 105, 97, 98, 108, 101, 115, 58, 0,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorIdx(
    mut v_x_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1180_) == 0 {
        let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1181_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1181_;
    } else {
        let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1182_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1182_;
    }
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(
    mut v_x_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1184_ = l_Lean_Meta_NativeEqTrueResult_ctorIdx(v_x_1183_);
    crate::leanh::lean_dec(v_x_1183_);
    return v_res_1184_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(
    mut v_t_1185_: *mut crate::leanh::LeanObject,
    mut v_k_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1185_) == 0 {
        let mut v_prf_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_prf_1187_ = crate::leanh::lean_ctor_get(v_t_1185_, 0);
        crate::leanh::lean_inc_ref(v_prf_1187_);
        crate::leanh::lean_dec_ref_known(v_t_1185_, 1);
        v___x_1188_ = crate::leanh::lean_apply_1(v_k_1186_, v_prf_1187_);
        return v___x_1188_;
    } else {
        return v_k_1186_;
    }
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim(
    mut v_motive_1189_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1190_: *mut crate::leanh::LeanObject,
    mut v_t_1191_: *mut crate::leanh::LeanObject,
    mut v_h_1192_: *mut crate::leanh::LeanObject,
    mut v_k_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1194_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1191_, v_k_1193_);
    return v___x_1194_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(
    mut v_motive_1195_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1196_: *mut crate::leanh::LeanObject,
    mut v_t_1197_: *mut crate::leanh::LeanObject,
    mut v_h_1198_: *mut crate::leanh::LeanObject,
    mut v_k_1199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ = l_Lean_Meta_NativeEqTrueResult_ctorElim(
        v_motive_1195_,
        v_ctorIdx_1196_,
        v_t_1197_,
        v_h_1198_,
        v_k_1199_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1196_);
    return v_res_1200_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(
    mut v_t_1201_: *mut crate::leanh::LeanObject,
    mut v_success_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1201_, v_success_1202_);
    return v___x_1203_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_success_elim(
    mut v_motive_1204_: *mut crate::leanh::LeanObject,
    mut v_t_1205_: *mut crate::leanh::LeanObject,
    mut v_h_1206_: *mut crate::leanh::LeanObject,
    mut v_success_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1205_, v_success_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(
    mut v_t_1209_: *mut crate::leanh::LeanObject,
    mut v_notTrue_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1209_, v_notTrue_1210_);
    return v___x_1211_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_notTrue_elim(
    mut v_motive_1212_: *mut crate::leanh::LeanObject,
    mut v_t_1213_: *mut crate::leanh::LeanObject,
    mut v_h_1214_: *mut crate::leanh::LeanObject,
    mut v_notTrue_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1213_, v_notTrue_1215_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = crate::leanh::lean_box(0);
    v___x_1218_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_1219_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1219_, 0, v___x_1218_);
    crate::leanh::lean_ctor_set(v___x_1219_, 1, v___x_1217_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0);
    v___x_1222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1222_, 0, v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___boxed(
    mut v___y_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
    return v_res_1224_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(
    mut v_msgData_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ = lean_st_ref_get(v___y_1229_);
    v_env_1232_ = crate::leanh::lean_ctor_get(v___x_1231_, 0);
    crate::leanh::lean_inc_ref(v_env_1232_);
    crate::leanh::lean_dec(v___x_1231_);
    v___x_1233_ = lean_st_ref_get(v___y_1227_);
    v_mctx_1234_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1234_);
    crate::leanh::lean_dec(v___x_1233_);
    v_lctx_1235_ = crate::leanh::lean_ctor_get(v___y_1226_, 2);
    v_options_1236_ = crate::leanh::lean_ctor_get(v___y_1228_, 2);
    crate::leanh::lean_inc_ref(v_options_1236_);
    crate::leanh::lean_inc_ref(v_lctx_1235_);
    v___x_1237_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1237_, 0, v_env_1232_);
    crate::leanh::lean_ctor_set(v___x_1237_, 1, v_mctx_1234_);
    crate::leanh::lean_ctor_set(v___x_1237_, 2, v_lctx_1235_);
    crate::leanh::lean_ctor_set(v___x_1237_, 3, v_options_1236_);
    v___x_1238_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    crate::leanh::lean_ctor_set(v___x_1238_, 1, v_msgData_1225_);
    v___x_1239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    return v___x_1239_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
    crate::leanh::lean_dec(v___y_1244_);
    crate::leanh::lean_dec_ref(v___y_1243_);
    crate::leanh::lean_dec(v___y_1242_);
    crate::leanh::lean_dec_ref(v___y_1241_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(
    mut v_msg_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1253_ = crate::leanh::lean_ctor_get(v___y_1250_, 5);
                v___x_1254_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
                v_a_1255_ = crate::leanh::lean_ctor_get(v___x_1254_, 0);
                v_isSharedCheck_1263_ = (!crate::leanh::lean_is_exclusive(v___x_1254_)) as u8;
                if v_isSharedCheck_1263_ == 0 {
                    v___x_1257_ = v___x_1254_;
                    v_isShared_1258_ = v_isSharedCheck_1263_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1255_);
                    crate::leanh::lean_dec(v___x_1254_);
                    v___x_1257_ = crate::leanh::lean_box(0);
                    v_isShared_1258_ = v_isSharedCheck_1263_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1253_);
                v___x_1259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1259_, 0, v_ref_1253_);
                crate::leanh::lean_ctor_set(v___x_1259_, 1, v_a_1255_);
                if v_isShared_1258_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1257_, 1);
                    crate::leanh::lean_ctor_set(v___x_1257_, 0, v___x_1259_);
                    v___x_1261_ = v___x_1257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
                    v___x_1261_ = v_reuseFailAlloc_1262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msg_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
    crate::leanh::lean_dec(v___y_1268_);
    crate::leanh::lean_dec_ref(v___y_1267_);
    crate::leanh::lean_dec(v___y_1266_);
    crate::leanh::lean_dec_ref(v___y_1265_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(
    mut v_x_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1283_: u8 = 0;
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1271_) == 0 {
                    v_a_1277_ = crate::leanh::lean_ctor_get(v_x_1271_, 0);
                    crate::leanh::lean_inc(v_a_1277_);
                    crate::leanh::lean_dec_ref_known(v_x_1271_, 1);
                    v___x_1278_ = l_Lean_stringToMessageData(v_a_1277_);
                    v___x_1279_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1278_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
                    return v___x_1279_;
                } else {
                    v_a_1280_ = crate::leanh::lean_ctor_get(v_x_1271_, 0);
                    v_isSharedCheck_1287_ = (!crate::leanh::lean_is_exclusive(v_x_1271_)) as u8;
                    if v_isSharedCheck_1287_ == 0 {
                        v___x_1282_ = v_x_1271_;
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1280_);
                        crate::leanh::lean_dec(v_x_1271_);
                        v___x_1282_ = crate::leanh::lean_box(0);
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1283_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1282_, 0);
                    v___x_1285_ = v___x_1282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
                    v___x_1285_ = v_reuseFailAlloc_1286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg___boxed(
    mut v_x_1288_: *mut crate::leanh::LeanObject,
    mut v___y_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
    crate::leanh::lean_dec(v___y_1292_);
    crate::leanh::lean_dec_ref(v___y_1291_);
    crate::leanh::lean_dec(v___y_1290_);
    crate::leanh::lean_dec_ref(v___y_1289_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(
    mut v_constName_1295_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_1296_: u8,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1302_ = lean_st_ref_get(v___y_1300_);
                v_env_1303_ = crate::leanh::lean_ctor_get(v___x_1302_, 0);
                crate::leanh::lean_inc_ref(v_env_1303_);
                crate::leanh::lean_dec(v___x_1302_);
                crate::leanh::lean_inc(v_constName_1295_);
                v___x_1304_ = lean_has_compile_error(v_env_1303_, v_constName_1295_);
                if v___x_1304_ == 0 {
                    v___x_1305_ = lean_st_ref_get(v___y_1300_);
                    v_env_1306_ = crate::leanh::lean_ctor_get(v___x_1305_, 0);
                    crate::leanh::lean_inc_ref(v_env_1306_);
                    crate::leanh::lean_dec(v___x_1305_);
                    v_options_1307_ = crate::leanh::lean_ctor_get(v___y_1299_, 2);
                    v___x_1308_ = l_Lean_Environment_evalConst___redArg(
                        v_env_1306_,
                        v_options_1307_,
                        v_constName_1295_,
                        v_checkMeta_1296_,
                    );
                    crate::leanh::lean_dec(v_constName_1295_);
                    crate::leanh::lean_dec_ref(v_env_1306_);
                    v___x_1309_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_1308_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
                    return v___x_1309_;
                } else {
                    v___x_1310_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
                    if crate::leanh::lean_obj_tag(v___x_1310_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1310_, 1);
                        v___x_1311_ = lean_st_ref_get(v___y_1300_);
                        v_env_1312_ = crate::leanh::lean_ctor_get(v___x_1311_, 0);
                        crate::leanh::lean_inc_ref(v_env_1312_);
                        crate::leanh::lean_dec(v___x_1311_);
                        v_options_1313_ = crate::leanh::lean_ctor_get(v___y_1299_, 2);
                        v___x_1314_ = l_Lean_Environment_evalConst___redArg(
                            v_env_1312_,
                            v_options_1313_,
                            v_constName_1295_,
                            v_checkMeta_1296_,
                        );
                        crate::leanh::lean_dec(v_constName_1295_);
                        crate::leanh::lean_dec_ref(v_env_1312_);
                        v___x_1315_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_1314_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
                        return v___x_1315_;
                    } else {
                        crate::leanh::lean_dec(v_constName_1295_);
                        v_a_1316_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1323_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1323_ == 0 {
                            v___x_1318_ = v___x_1310_;
                            v_isShared_1319_ = v_isSharedCheck_1323_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1316_);
                            crate::leanh::lean_dec(v___x_1310_);
                            v___x_1318_ = crate::leanh::lean_box(0);
                            v_isShared_1319_ = v_isSharedCheck_1323_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1319_ == 0 {
                    v___x_1321_ = v___x_1318_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
                    v___x_1321_ = v_reuseFailAlloc_1322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg___boxed(
    mut v_constName_1324_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkMeta_boxed_1331_: u8 = 0;
    let mut v_res_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1331_ = (crate::leanh::lean_unbox(v_checkMeta_1325_) as u8);
    v_res_1332_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_1324_, v_checkMeta_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
    crate::leanh::lean_dec(v___y_1329_);
    crate::leanh::lean_dec_ref(v___y_1328_);
    crate::leanh::lean_dec(v___y_1327_);
    crate::leanh::lean_dec_ref(v___y_1326_);
    return v_res_1332_;
}
pub unsafe fn l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
    mut v_auxDeclName_1333_: *mut crate::leanh::LeanObject,
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
    mut v_a_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: u8 = 0;
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = 1;
    v___x_1340_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_auxDeclName_1333_, v___x_1339_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
    return v___x_1340_;
}
pub unsafe fn l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(
    mut v_auxDeclName_1341_: *mut crate::leanh::LeanObject,
    mut v_a_1342_: *mut crate::leanh::LeanObject,
    mut v_a_1343_: *mut crate::leanh::LeanObject,
    mut v_a_1344_: *mut crate::leanh::LeanObject,
    mut v_a_1345_: *mut crate::leanh::LeanObject,
    mut v_a_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1347_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
        v_auxDeclName_1341_,
        v_a_1342_,
        v_a_1343_,
        v_a_1344_,
        v_a_1345_,
    );
    crate::leanh::lean_dec(v_a_1345_);
    crate::leanh::lean_dec_ref(v_a_1344_);
    crate::leanh::lean_dec(v_a_1343_);
    crate::leanh::lean_dec_ref(v_a_1342_);
    return v_res_1347_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(
    mut v_00_u03b1_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
    return v___x_1354_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___boxed(
    mut v_00_u03b1_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(v_00_u03b1_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
    crate::leanh::lean_dec(v___y_1359_);
    crate::leanh::lean_dec_ref(v___y_1358_);
    crate::leanh::lean_dec(v___y_1357_);
    crate::leanh::lean_dec_ref(v___y_1356_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(
    mut v_00_u03b1_1362_: *mut crate::leanh::LeanObject,
    mut v_constName_1363_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_1364_: u8,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_1363_, v_checkMeta_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
    return v___x_1370_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___boxed(
    mut v_00_u03b1_1371_: *mut crate::leanh::LeanObject,
    mut v_constName_1372_: *mut crate::leanh::LeanObject,
    mut v_checkMeta_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkMeta_boxed_1379_: u8 = 0;
    let mut v_res_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1379_ = (crate::leanh::lean_unbox(v_checkMeta_1373_) as u8);
    v_res_1380_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(v_00_u03b1_1371_, v_constName_1372_, v_checkMeta_boxed_1379_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
    crate::leanh::lean_dec(v___y_1377_);
    crate::leanh::lean_dec_ref(v___y_1376_);
    crate::leanh::lean_dec(v___y_1375_);
    crate::leanh::lean_dec_ref(v___y_1374_);
    return v_res_1380_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(
    mut v_00_u03b1_1381_: *mut crate::leanh::LeanObject,
    mut v_x_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
    return v___x_1388_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b1_1389_: *mut crate::leanh::LeanObject,
    mut v_x_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
    mut v___y_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(v_00_u03b1_1389_, v_x_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
    crate::leanh::lean_dec(v___y_1394_);
    crate::leanh::lean_dec_ref(v___y_1393_);
    crate::leanh::lean_dec(v___y_1392_);
    crate::leanh::lean_dec_ref(v___y_1391_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1397_: *mut crate::leanh::LeanObject,
    mut v_msg_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
    mut v___y_1400_: *mut crate::leanh::LeanObject,
    mut v___y_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1405_: *mut crate::leanh::LeanObject,
    mut v_msg_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_1405_, v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
    crate::leanh::lean_dec(v___y_1410_);
    crate::leanh::lean_dec_ref(v___y_1409_);
    crate::leanh::lean_dec(v___y_1408_);
    crate::leanh::lean_dec_ref(v___y_1407_);
    return v_res_1412_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
    mut v_e_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: u8 = 0;
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_unused_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1416_ = l_Lean_Expr_hasMVar(v_e_1413_);
                if v___x_1416_ == 0 {
                    v___x_1417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1417_, 0, v_e_1413_);
                    return v___x_1417_;
                } else {
                    v___x_1418_ = lean_st_ref_get(v___y_1414_);
                    v_mctx_1419_ = crate::leanh::lean_ctor_get(v___x_1418_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1419_);
                    crate::leanh::lean_dec(v___x_1418_);
                    v___x_1420_ = l_Lean_instantiateMVarsCore(v_mctx_1419_, v_e_1413_);
                    v_fst_1421_ = crate::leanh::lean_ctor_get(v___x_1420_, 0);
                    crate::leanh::lean_inc(v_fst_1421_);
                    v_snd_1422_ = crate::leanh::lean_ctor_get(v___x_1420_, 1);
                    crate::leanh::lean_inc(v_snd_1422_);
                    crate::leanh::lean_dec_ref(v___x_1420_);
                    v___x_1423_ = lean_st_ref_take(v___y_1414_);
                    v_cache_1424_ = crate::leanh::lean_ctor_get(v___x_1423_, 1);
                    v_zetaDeltaFVarIds_1425_ = crate::leanh::lean_ctor_get(v___x_1423_, 2);
                    v_postponed_1426_ = crate::leanh::lean_ctor_get(v___x_1423_, 3);
                    v_diag_1427_ = crate::leanh::lean_ctor_get(v___x_1423_, 4);
                    v_isSharedCheck_1436_ = (!crate::leanh::lean_is_exclusive(v___x_1423_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v_unused_1437_ = crate::leanh::lean_ctor_get(v___x_1423_, 0);
                        crate::leanh::lean_dec(v_unused_1437_);
                        v___x_1429_ = v___x_1423_;
                        v_isShared_1430_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1427_);
                        crate::leanh::lean_inc(v_postponed_1426_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1425_);
                        crate::leanh::lean_inc(v_cache_1424_);
                        crate::leanh::lean_dec(v___x_1423_);
                        v___x_1429_ = crate::leanh::lean_box(0);
                        v_isShared_1430_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1430_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v_snd_1422_);
                    v___x_1432_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_snd_1422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_cache_1424_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1435_,
                        2,
                        v_zetaDeltaFVarIds_1425_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_postponed_1426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_diag_1427_);
                    v___x_1432_ = v_reuseFailAlloc_1435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1433_ = lean_st_ref_set(v___y_1414_, v___x_1432_);
                v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1434_, 0, v_fst_1421_);
                return v___x_1434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(
    mut v_e_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
        v_e_1438_,
        v___y_1439_,
    );
    crate::leanh::lean_dec(v___y_1439_);
    return v_res_1441_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(
    mut v_e_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
        v_e_1442_,
        v___y_1444_,
    );
    return v___x_1448_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(
    mut v_e_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(
        v_e_1449_,
        v___y_1450_,
        v___y_1451_,
        v___y_1452_,
        v___y_1453_,
    );
    crate::leanh::lean_dec(v___y_1453_);
    crate::leanh::lean_dec_ref(v___y_1452_);
    crate::leanh::lean_dec(v___y_1451_);
    crate::leanh::lean_dec_ref(v___y_1450_);
    return v_res_1455_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
    mut v_kind_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut v_unused_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1459_ = lean_st_ref_get(v___y_1457_);
                v_auxDeclNGen_1460_ = crate::leanh::lean_ctor_get(v___x_1459_, 3);
                crate::leanh::lean_inc_ref(v_auxDeclNGen_1460_);
                crate::leanh::lean_dec(v___x_1459_);
                v___x_1461_ = lean_st_ref_get(v___y_1457_);
                v_env_1462_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                crate::leanh::lean_inc_ref(v_env_1462_);
                crate::leanh::lean_dec(v___x_1461_);
                v___x_1463_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_1462_,
                    v_auxDeclNGen_1460_,
                    v_kind_1456_,
                );
                v_fst_1464_ = crate::leanh::lean_ctor_get(v___x_1463_, 0);
                crate::leanh::lean_inc(v_fst_1464_);
                v_snd_1465_ = crate::leanh::lean_ctor_get(v___x_1463_, 1);
                crate::leanh::lean_inc(v_snd_1465_);
                crate::leanh::lean_dec_ref(v___x_1463_);
                v___x_1466_ = lean_st_ref_take(v___y_1457_);
                v_env_1467_ = crate::leanh::lean_ctor_get(v___x_1466_, 0);
                v_nextMacroScope_1468_ = crate::leanh::lean_ctor_get(v___x_1466_, 1);
                v_ngen_1469_ = crate::leanh::lean_ctor_get(v___x_1466_, 2);
                v_traceState_1470_ = crate::leanh::lean_ctor_get(v___x_1466_, 4);
                v_cache_1471_ = crate::leanh::lean_ctor_get(v___x_1466_, 5);
                v_messages_1472_ = crate::leanh::lean_ctor_get(v___x_1466_, 6);
                v_infoState_1473_ = crate::leanh::lean_ctor_get(v___x_1466_, 7);
                v_snapshotTasks_1474_ = crate::leanh::lean_ctor_get(v___x_1466_, 8);
                v_isSharedCheck_1483_ = (!crate::leanh::lean_is_exclusive(v___x_1466_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v_unused_1484_ = crate::leanh::lean_ctor_get(v___x_1466_, 3);
                    crate::leanh::lean_dec(v_unused_1484_);
                    v___x_1476_ = v___x_1466_;
                    v_isShared_1477_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1474_);
                    crate::leanh::lean_inc(v_infoState_1473_);
                    crate::leanh::lean_inc(v_messages_1472_);
                    crate::leanh::lean_inc(v_cache_1471_);
                    crate::leanh::lean_inc(v_traceState_1470_);
                    crate::leanh::lean_inc(v_ngen_1469_);
                    crate::leanh::lean_inc(v_nextMacroScope_1468_);
                    crate::leanh::lean_inc(v_env_1467_);
                    crate::leanh::lean_dec(v___x_1466_);
                    v___x_1476_ = crate::leanh::lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1476_, 3, v_snd_1465_);
                    v___x_1479_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_env_1467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_nextMacroScope_1468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_ngen_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_snd_1465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_traceState_1470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 5, v_cache_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 6, v_messages_1472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 7, v_infoState_1473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 8, v_snapshotTasks_1474_);
                    v___x_1479_ = v_reuseFailAlloc_1482_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1480_ = lean_st_ref_set(v___y_1457_, v___x_1479_);
                v___x_1481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1481_, 0, v_fst_1464_);
                return v___x_1481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(
    mut v_kind_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
        v_kind_1485_,
        v___y_1486_,
    );
    crate::leanh::lean_dec(v___y_1486_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(
    mut v_kind_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
        v_kind_1489_,
        v___y_1493_,
    );
    return v___x_1495_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(
    mut v_kind_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
    mut v___y_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(
        v_kind_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
        v___y_1500_,
    );
    crate::leanh::lean_dec(v___y_1500_);
    crate::leanh::lean_dec_ref(v___y_1499_);
    crate::leanh::lean_dec(v___y_1498_);
    crate::leanh::lean_dec_ref(v___y_1497_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(
    mut v_opts_1503_: *mut crate::leanh::LeanObject,
    mut v_opt_1504_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1505_ = crate::leanh::lean_ctor_get(v_opt_1504_, 0);
    v_defValue_1506_ = crate::leanh::lean_ctor_get(v_opt_1504_, 1);
    v_map_1507_ = crate::leanh::lean_ctor_get(v_opts_1503_, 0);
    v___x_1508_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1507_,
            v_name_1505_,
        );
    if crate::leanh::lean_obj_tag(v___x_1508_) == 0 {
        let mut v___x_1509_: u8 = 0;
        v___x_1509_ = (crate::leanh::lean_unbox(v_defValue_1506_) as u8);
        return v___x_1509_;
    } else {
        let mut v_val_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1510_ = crate::leanh::lean_ctor_get(v___x_1508_, 0);
        crate::leanh::lean_inc(v_val_1510_);
        crate::leanh::lean_dec_ref_known(v___x_1508_, 1);
        if crate::leanh::lean_obj_tag(v_val_1510_) == 1 {
            let mut v_v_1511_: u8 = 0;
            v_v_1511_ = crate::leanh::lean_ctor_get_uint8(v_val_1510_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1510_, 0);
            return v_v_1511_;
        } else {
            let mut v___x_1512_: u8 = 0;
            crate::leanh::lean_dec(v_val_1510_);
            v___x_1512_ = (crate::leanh::lean_unbox(v_defValue_1506_) as u8);
            return v___x_1512_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(
    mut v_opts_1513_: *mut crate::leanh::LeanObject,
    mut v_opt_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ =
        l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v_opts_1513_, v_opt_1514_);
    crate::leanh::lean_dec_ref(v_opt_1514_);
    crate::leanh::lean_dec_ref(v_opts_1513_);
    v_r_1516_ = crate::leanh::lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
    mut v_opts_1517_: *mut crate::leanh::LeanObject,
    mut v_opt_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1519_ = crate::leanh::lean_ctor_get(v_opt_1518_, 0);
    v_defValue_1520_ = crate::leanh::lean_ctor_get(v_opt_1518_, 1);
    v_map_1521_ = crate::leanh::lean_ctor_get(v_opts_1517_, 0);
    v___x_1522_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1521_,
            v_name_1519_,
        );
    if crate::leanh::lean_obj_tag(v___x_1522_) == 0 {
        crate::leanh::lean_inc(v_defValue_1520_);
        return v_defValue_1520_;
    } else {
        let mut v_val_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1523_ = crate::leanh::lean_ctor_get(v___x_1522_, 0);
        crate::leanh::lean_inc(v_val_1523_);
        crate::leanh::lean_dec_ref_known(v___x_1522_, 1);
        if crate::leanh::lean_obj_tag(v_val_1523_) == 3 {
            let mut v_v_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_1524_ = crate::leanh::lean_ctor_get(v_val_1523_, 0);
            crate::leanh::lean_inc(v_v_1524_);
            crate::leanh::lean_dec_ref_known(v_val_1523_, 1);
            return v_v_1524_;
        } else {
            crate::leanh::lean_dec(v_val_1523_);
            crate::leanh::lean_inc(v_defValue_1520_);
            return v_defValue_1520_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(
    mut v_opts_1525_: *mut crate::leanh::LeanObject,
    mut v_opt_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1527_ =
        l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_1525_, v_opt_1526_);
    crate::leanh::lean_dec_ref(v_opt_1526_);
    crate::leanh::lean_dec_ref(v_opts_1525_);
    return v_res_1527_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
    mut v_o_1531_: *mut crate::leanh::LeanObject,
    mut v_k_1532_: *mut crate::leanh::LeanObject,
    mut v_v_1533_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1535_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1534_ = crate::leanh::lean_ctor_get(v_o_1531_, 0);
                v_hasTrace_1535_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_1531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1549_ = (!crate::leanh::lean_is_exclusive(v_o_1531_)) as u8;
                if v_isSharedCheck_1549_ == 0 {
                    v___x_1537_ = v_o_1531_;
                    v_isShared_1538_ = v_isSharedCheck_1549_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_1534_);
                    crate::leanh::lean_dec(v_o_1531_);
                    v___x_1537_ = crate::leanh::lean_box(0);
                    v_isShared_1538_ = v_isSharedCheck_1549_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1539_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_1539_, 0 as u32, v_v_1533_);
                crate::leanh::lean_inc(v_k_1532_);
                v___x_1540_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1532_, v___x_1539_, v_map_1534_);
                if v_hasTrace_1535_ == 0 {
                    v___x_1541_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1;
                    v___x_1542_ = l_Lean_Name_isPrefixOf(v___x_1541_, v_k_1532_);
                    crate::leanh::lean_dec(v_k_1532_);
                    if v_isShared_1538_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1540_);
                        v___x_1544_ = v___x_1537_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1545_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1540_);
                        v___x_1544_ = v_reuseFailAlloc_1545_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_1532_);
                    if v_isShared_1538_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1540_);
                        v___x_1547_ = v___x_1537_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1548_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1540_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1548_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1535_,
                        );
                        v___x_1547_ = v_reuseFailAlloc_1548_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1544_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1542_,
                );
                return v___x_1544_;
            }
            3 => {
                return v___x_1547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(
    mut v_o_1550_: *mut crate::leanh::LeanObject,
    mut v_k_1551_: *mut crate::leanh::LeanObject,
    mut v_v_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_1553_: u8 = 0;
    let mut v_res_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1553_ = (crate::leanh::lean_unbox(v_v_1552_) as u8);
    v_res_1554_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
            v_o_1550_,
            v_k_1551_,
            v_v_boxed_1553_,
        );
    return v_res_1554_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
    mut v_opts_1555_: *mut crate::leanh::LeanObject,
    mut v_opt_1556_: *mut crate::leanh::LeanObject,
    mut v_val_1557_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1558_ = crate::leanh::lean_ctor_get(v_opt_1556_, 0);
    crate::leanh::lean_inc(v_name_1558_);
    crate::leanh::lean_dec_ref(v_opt_1556_);
    v___x_1559_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
            v_opts_1555_,
            v_name_1558_,
            v_val_1557_,
        );
    return v___x_1559_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(
    mut v_opts_1560_: *mut crate::leanh::LeanObject,
    mut v_opt_1561_: *mut crate::leanh::LeanObject,
    mut v_val_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_1563_: u8 = 0;
    let mut v_res_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_1563_ = (crate::leanh::lean_unbox(v_val_1562_) as u8);
    v_res_1564_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
        v_opts_1560_,
        v_opt_1561_,
        v_val_boxed_1563_,
    );
    return v_res_1564_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__0;
    v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__2;
    v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
    return v___x_1570_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1572_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__4;
    v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = crate::leanh::lean_box(0);
    v___x_1578_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__7;
    v___x_1579_ = l_Lean_mkConst(v___x_1578_, v___x_1577_);
    return v___x_1579_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1580_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9,
    );
    v___x_1582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10,
    );
    v___x_1584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1584_, 0, v___x_1583_);
    crate::leanh::lean_ctor_set(v___x_1584_, 1, v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10,
    );
    v___x_1586_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
    crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1585_);
    crate::leanh::lean_ctor_set(v___x_1586_, 2, v___x_1585_);
    crate::leanh::lean_ctor_set(v___x_1586_, 3, v___x_1585_);
    crate::leanh::lean_ctor_set(v___x_1586_, 4, v___x_1585_);
    crate::leanh::lean_ctor_set(v___x_1586_, 5, v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn l_Lean_Meta_nativeEqTrue___lam__0(
    mut v___x_1587_: *mut crate::leanh::LeanObject,
    mut v___x_1588_: *mut crate::leanh::LeanObject,
    mut v___x_1589_: *mut crate::leanh::LeanObject,
    mut v_tacticName_1590_: *mut crate::leanh::LeanObject,
    mut v_a_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: u8 = 0;
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___y_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: u8 = 0;
    let mut v_a_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v___y_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: u8 = 0;
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: u8 = 0;
    let mut v___y_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: u8 = 0;
    let mut v___y_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1697_: u8 = 0;
    let mut v_inheritedTraceOptions_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: u8 = 0;
    let mut v___y_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1708_: u8 = 0;
    let mut v___y_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1723_: u8 = 0;
    let mut v_inheritedTraceOptions_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: u8 = 0;
    let mut v___y_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1731_: u8 = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut v_unused_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1755_: u8 = 0;
    let mut v___y_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1772_: u8 = 0;
    let mut v_inheritedTraceOptions_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v_env_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut v_unused_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1791_: u8 = 0;
    let mut v___y_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1795_: u8 = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v_unused_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___y_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1831_: u8 = 0;
    let mut v_inheritedTraceOptions_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v_env_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u8 = 0;
    let mut v___x_1844_: u8 = 0;
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1868_: u8 = 0;
    let mut v_unused_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v_reuseFailAlloc_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_unused_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_unused_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1609_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
                    v___x_1587_,
                    v___y_1595_,
                );
                v_a_1610_ = crate::leanh::lean_ctor_get(v___x_1609_, 0);
                v_isSharedCheck_1878_ = (!crate::leanh::lean_is_exclusive(v___x_1609_)) as u8;
                if v_isSharedCheck_1878_ == 0 {
                    v___x_1612_ = v___x_1609_;
                    v_isShared_1613_ = v_isSharedCheck_1878_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1610_);
                    crate::leanh::lean_dec(v___x_1609_);
                    v___x_1612_ = crate::leanh::lean_box(0);
                    v_isShared_1613_ = v_isSharedCheck_1878_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1600_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1599_);
                    v___x_1601_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_1602_ = l_Lean_MessageData_ofName(v_tacticName_1590_);
                    v___x_1603_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1603_, 0, v___x_1601_);
                    crate::leanh::lean_ctor_set(v___x_1603_, 1, v___x_1602_);
                    v___x_1604_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3,
                    );
                    v___x_1605_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1605_, 0, v___x_1603_);
                    crate::leanh::lean_ctor_set(v___x_1605_, 1, v___x_1604_);
                    v___x_1606_ = l_Lean_Exception_toMessageData(v___y_1598_);
                    v___x_1607_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1607_, 0, v___x_1605_);
                    crate::leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
                    v___x_1608_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1607_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
                    crate::leanh::lean_dec_ref(v___y_1594_);
                    return v___x_1608_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1598_);
                    crate::leanh::lean_dec_ref(v___y_1594_);
                    crate::leanh::lean_dec(v_tacticName_1590_);
                    return v___y_1599_;
                }
            }
            2 => {
                v___x_1640_ = lean_st_ref_take(v___y_1595_);
                v_env_1641_ = crate::leanh::lean_ctor_get(v___x_1640_, 0);
                v_nextMacroScope_1642_ = crate::leanh::lean_ctor_get(v___x_1640_, 1);
                v_ngen_1643_ = crate::leanh::lean_ctor_get(v___x_1640_, 2);
                v_auxDeclNGen_1644_ = crate::leanh::lean_ctor_get(v___x_1640_, 3);
                v_traceState_1645_ = crate::leanh::lean_ctor_get(v___x_1640_, 4);
                v_messages_1646_ = crate::leanh::lean_ctor_get(v___x_1640_, 6);
                v_infoState_1647_ = crate::leanh::lean_ctor_get(v___x_1640_, 7);
                v_snapshotTasks_1648_ = crate::leanh::lean_ctor_get(v___x_1640_, 8);
                v_isSharedCheck_1876_ = (!crate::leanh::lean_is_exclusive(v___x_1640_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v_unused_1877_ = crate::leanh::lean_ctor_get(v___x_1640_, 5);
                    crate::leanh::lean_dec(v_unused_1877_);
                    v___x_1650_ = v___x_1640_;
                    v_isShared_1651_ = v_isSharedCheck_1876_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1648_);
                    crate::leanh::lean_inc(v_infoState_1647_);
                    crate::leanh::lean_inc(v_messages_1646_);
                    crate::leanh::lean_inc(v_traceState_1645_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1644_);
                    crate::leanh::lean_inc(v_ngen_1643_);
                    crate::leanh::lean_inc(v_nextMacroScope_1642_);
                    crate::leanh::lean_inc(v_env_1641_);
                    crate::leanh::lean_dec(v___x_1640_);
                    v___x_1650_ = crate::leanh::lean_box(0);
                    v_isShared_1651_ = v_isSharedCheck_1876_;
                    state = 7;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_1615_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_1615_, 1);
                    v___x_1616_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
                        v_a_1610_,
                        v___y_1592_,
                        v___y_1593_,
                        v___y_1594_,
                        v___y_1595_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1616_) == 0 {
                        crate::leanh::lean_dec_ref(v___y_1594_);
                        crate::leanh::lean_dec(v_tacticName_1590_);
                        return v___x_1616_;
                    } else {
                        v_a_1617_ = crate::leanh::lean_ctor_get(v___x_1616_, 0);
                        crate::leanh::lean_inc(v_a_1617_);
                        v___x_1618_ = l_Lean_Exception_isInterrupt(v_a_1617_);
                        if v___x_1618_ == 0 {
                            crate::leanh::lean_inc(v_a_1617_);
                            v___x_1619_ = l_Lean_Exception_isRuntime(v_a_1617_);
                            v___y_1598_ = v_a_1617_;
                            v___y_1599_ = v___x_1616_;
                            v___y_1600_ = v___x_1619_;
                            state = 1;
                            continue;
                        } else {
                            v___y_1598_ = v_a_1617_;
                            v___y_1599_ = v___x_1616_;
                            v___y_1600_ = v___x_1618_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1610_);
                    crate::leanh::lean_dec_ref(v___y_1594_);
                    crate::leanh::lean_dec(v_tacticName_1590_);
                    v_a_1620_ = crate::leanh::lean_ctor_get(v___y_1615_, 0);
                    v_isSharedCheck_1627_ = (!crate::leanh::lean_is_exclusive(v___y_1615_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v___x_1622_ = v___y_1615_;
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1620_);
                        crate::leanh::lean_dec(v___y_1615_);
                        v___x_1622_ = crate::leanh::lean_box(0);
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1623_ == 0 {
                    v___x_1625_ = v___x_1622_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
                    v___x_1625_ = v_reuseFailAlloc_1626_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1625_;
            }
            6 => {
                if v___y_1631_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1630_);
                    v___x_1632_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    crate::leanh::lean_inc(v_tacticName_1590_);
                    v___x_1633_ = l_Lean_MessageData_ofName(v_tacticName_1590_);
                    v___x_1634_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                    crate::leanh::lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                    v___x_1635_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5,
                    );
                    v___x_1636_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1636_, 0, v___x_1634_);
                    crate::leanh::lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                    v___x_1637_ = l_Lean_Exception_toMessageData(v___y_1629_);
                    v___x_1638_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1638_, 0, v___x_1636_);
                    crate::leanh::lean_ctor_set(v___x_1638_, 1, v___x_1637_);
                    v___x_1639_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1638_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
                    v___y_1615_ = v___x_1639_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1629_);
                    v___y_1615_ = v___y_1630_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_1652_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8,
                );
                crate::leanh::lean_inc_n(v_a_1610_, 3);
                v___x_1653_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1653_, 0, v_a_1610_);
                crate::leanh::lean_ctor_set(v___x_1653_, 1, v___x_1588_);
                crate::leanh::lean_ctor_set(v___x_1653_, 2, v___x_1652_);
                v___x_1654_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1654_, 0, v_a_1610_);
                crate::leanh::lean_ctor_set(v___x_1654_, 1, v___x_1589_);
                v___x_1655_ = l_Lean_markMeta(v_env_1641_, v_a_1610_);
                v___x_1656_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_1651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1650_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v___x_1650_, 0, v___x_1655_);
                    v___x_1658_ = v___x_1650_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_nextMacroScope_1642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_ngen_1643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_auxDeclNGen_1644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_traceState_1645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 6, v_messages_1646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 7, v_infoState_1647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 8, v_snapshotTasks_1648_);
                    v___x_1658_ = v_reuseFailAlloc_1875_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1659_ = lean_st_ref_set(v___y_1595_, v___x_1658_);
                v___x_1660_ = lean_st_ref_take(v___y_1593_);
                v_mctx_1661_ = crate::leanh::lean_ctor_get(v___x_1660_, 0);
                v_zetaDeltaFVarIds_1662_ = crate::leanh::lean_ctor_get(v___x_1660_, 2);
                v_postponed_1663_ = crate::leanh::lean_ctor_get(v___x_1660_, 3);
                v_diag_1664_ = crate::leanh::lean_ctor_get(v___x_1660_, 4);
                v_isSharedCheck_1873_ = (!crate::leanh::lean_is_exclusive(v___x_1660_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v_unused_1874_ = crate::leanh::lean_ctor_get(v___x_1660_, 1);
                    crate::leanh::lean_dec(v_unused_1874_);
                    v___x_1666_ = v___x_1660_;
                    v_isShared_1667_ = v_isSharedCheck_1873_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1664_);
                    crate::leanh::lean_inc(v_postponed_1663_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1662_);
                    crate::leanh::lean_inc(v_mctx_1661_);
                    crate::leanh::lean_dec(v___x_1660_);
                    v___x_1666_ = crate::leanh::lean_box(0);
                    v_isShared_1667_ = v_isSharedCheck_1873_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1668_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_1667_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1666_, 1, v___x_1668_);
                    v___x_1670_ = v___x_1666_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_mctx_1661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1668_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1872_,
                        2,
                        v_zetaDeltaFVarIds_1662_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_postponed_1663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_diag_1664_);
                    v___x_1670_ = v_reuseFailAlloc_1872_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1671_ = lean_st_ref_set(v___y_1593_, v___x_1670_);
                v___x_1672_ = lean_st_ref_get(v___y_1595_);
                v_options_1673_ = crate::leanh::lean_ctor_get(v___y_1594_, 2);
                v_env_1674_ = crate::leanh::lean_ctor_get(v___x_1672_, 0);
                crate::leanh::lean_inc_ref(v_env_1674_);
                crate::leanh::lean_dec(v___x_1672_);
                v___x_1675_ = crate::leanh::lean_box(1);
                v___x_1676_ = 1;
                v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1653_);
                crate::leanh::lean_ctor_set(v___x_1677_, 1, v_a_1591_);
                crate::leanh::lean_ctor_set(v___x_1677_, 2, v___x_1675_);
                crate::leanh::lean_ctor_set(v___x_1677_, 3, v___x_1654_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1677_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_1676_,
                );
                if v_isShared_1613_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1612_, 1);
                    crate::leanh::lean_ctor_set(v___x_1612_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1612_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1677_);
                    v___x_1679_ = v_reuseFailAlloc_1871_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1680_ = 1;
                v___x_1681_ = 0;
                v___x_1751_ = l_Lean_Elab_async;
                crate::leanh::lean_inc_ref(v_options_1673_);
                v___x_1752_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
                    v_options_1673_,
                    v___x_1751_,
                    v___x_1681_,
                );
                v___x_1753_ = l_Lean_diagnostics;
                v___x_1815_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(
                    v___x_1752_,
                    v___x_1753_,
                );
                v___x_1870_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1674_);
                crate::leanh::lean_dec_ref(v_env_1674_);
                if v___x_1870_ == 0 {
                    if v___x_1815_ == 0 {
                        crate::leanh::lean_inc_ref(v___y_1594_);
                        v___y_1817_ = v___y_1594_;
                        v___y_1818_ = v___y_1595_;
                        state = 23;
                        continue;
                    } else {
                        v___y_1850_ = v___x_1870_;
                        state = 26;
                        continue;
                    }
                } else {
                    v___y_1850_ = v___x_1815_;
                    state = 26;
                    continue;
                }
            }
            12 => {
                v___x_1700_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
                    v___y_1683_,
                    v___y_1685_,
                );
                v___x_1701_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1701_, 0, v_fileName_1686_);
                crate::leanh::lean_ctor_set(v___x_1701_, 1, v_fileMap_1687_);
                crate::leanh::lean_ctor_set(v___x_1701_, 2, v___y_1683_);
                crate::leanh::lean_ctor_set(v___x_1701_, 3, v_currRecDepth_1688_);
                crate::leanh::lean_ctor_set(v___x_1701_, 4, v___x_1700_);
                crate::leanh::lean_ctor_set(v___x_1701_, 5, v_ref_1689_);
                crate::leanh::lean_ctor_set(v___x_1701_, 6, v_currNamespace_1690_);
                crate::leanh::lean_ctor_set(v___x_1701_, 7, v_openDecls_1691_);
                crate::leanh::lean_ctor_set(v___x_1701_, 8, v_initHeartbeats_1692_);
                crate::leanh::lean_ctor_set(v___x_1701_, 9, v_maxHeartbeats_1693_);
                crate::leanh::lean_ctor_set(v___x_1701_, 10, v_quotContext_1694_);
                crate::leanh::lean_ctor_set(v___x_1701_, 11, v_currMacroScope_1695_);
                crate::leanh::lean_ctor_set(v___x_1701_, 12, v_cancelTk_x3f_1696_);
                crate::leanh::lean_ctor_set(v___x_1701_, 13, v_inheritedTraceOptions_1698_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1701_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_1684_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1701_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1697_,
                );
                v___x_1702_ = l_Lean_addAndCompile(
                    v___x_1679_,
                    v___x_1680_,
                    v___x_1681_,
                    v___x_1701_,
                    v___y_1699_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1701_, 14);
                if crate::leanh::lean_obj_tag(v___x_1702_) == 0 {
                    v___y_1615_ = v___x_1702_;
                    state = 3;
                    continue;
                } else {
                    v_a_1703_ = crate::leanh::lean_ctor_get(v___x_1702_, 0);
                    crate::leanh::lean_inc(v_a_1703_);
                    v___x_1704_ = l_Lean_Exception_isInterrupt(v_a_1703_);
                    if v___x_1704_ == 0 {
                        crate::leanh::lean_inc(v_a_1703_);
                        v___x_1705_ = l_Lean_Exception_isRuntime(v_a_1703_);
                        v___y_1629_ = v_a_1703_;
                        v___y_1630_ = v___x_1702_;
                        v___y_1631_ = v___x_1705_;
                        state = 6;
                        continue;
                    } else {
                        v___y_1629_ = v_a_1703_;
                        v___y_1630_ = v___x_1702_;
                        v___y_1631_ = v___x_1704_;
                        state = 6;
                        continue;
                    }
                }
            }
            13 => {
                v_fileName_1712_ = crate::leanh::lean_ctor_get(v___y_1710_, 0);
                crate::leanh::lean_inc_ref(v_fileName_1712_);
                v_fileMap_1713_ = crate::leanh::lean_ctor_get(v___y_1710_, 1);
                crate::leanh::lean_inc_ref(v_fileMap_1713_);
                v_currRecDepth_1714_ = crate::leanh::lean_ctor_get(v___y_1710_, 3);
                crate::leanh::lean_inc(v_currRecDepth_1714_);
                v_ref_1715_ = crate::leanh::lean_ctor_get(v___y_1710_, 5);
                crate::leanh::lean_inc(v_ref_1715_);
                v_currNamespace_1716_ = crate::leanh::lean_ctor_get(v___y_1710_, 6);
                crate::leanh::lean_inc(v_currNamespace_1716_);
                v_openDecls_1717_ = crate::leanh::lean_ctor_get(v___y_1710_, 7);
                crate::leanh::lean_inc(v_openDecls_1717_);
                v_initHeartbeats_1718_ = crate::leanh::lean_ctor_get(v___y_1710_, 8);
                crate::leanh::lean_inc(v_initHeartbeats_1718_);
                v_maxHeartbeats_1719_ = crate::leanh::lean_ctor_get(v___y_1710_, 9);
                crate::leanh::lean_inc(v_maxHeartbeats_1719_);
                v_quotContext_1720_ = crate::leanh::lean_ctor_get(v___y_1710_, 10);
                crate::leanh::lean_inc(v_quotContext_1720_);
                v_currMacroScope_1721_ = crate::leanh::lean_ctor_get(v___y_1710_, 11);
                crate::leanh::lean_inc(v_currMacroScope_1721_);
                v_cancelTk_x3f_1722_ = crate::leanh::lean_ctor_get(v___y_1710_, 12);
                crate::leanh::lean_inc(v_cancelTk_x3f_1722_);
                v_suppressElabErrors_1723_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1710_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1724_ = crate::leanh::lean_ctor_get(v___y_1710_, 13);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1724_);
                crate::leanh::lean_dec_ref(v___y_1710_);
                v___y_1683_ = v___y_1707_;
                v___y_1684_ = v___y_1708_;
                v___y_1685_ = v___y_1709_;
                v_fileName_1686_ = v_fileName_1712_;
                v_fileMap_1687_ = v_fileMap_1713_;
                v_currRecDepth_1688_ = v_currRecDepth_1714_;
                v_ref_1689_ = v_ref_1715_;
                v_currNamespace_1690_ = v_currNamespace_1716_;
                v_openDecls_1691_ = v_openDecls_1717_;
                v_initHeartbeats_1692_ = v_initHeartbeats_1718_;
                v_maxHeartbeats_1693_ = v_maxHeartbeats_1719_;
                v_quotContext_1694_ = v_quotContext_1720_;
                v_currMacroScope_1695_ = v_currMacroScope_1721_;
                v_cancelTk_x3f_1696_ = v_cancelTk_x3f_1722_;
                v_suppressElabErrors_1697_ = v_suppressElabErrors_1723_;
                v_inheritedTraceOptions_1698_ = v_inheritedTraceOptions_1724_;
                v___y_1699_ = v___y_1711_;
                state = 12;
                continue;
            }
            14 => {
                if v___y_1731_ == 0 {
                    v___x_1732_ = lean_st_ref_take(v___y_1728_);
                    v_env_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                    v_nextMacroScope_1734_ = crate::leanh::lean_ctor_get(v___x_1732_, 1);
                    v_ngen_1735_ = crate::leanh::lean_ctor_get(v___x_1732_, 2);
                    v_auxDeclNGen_1736_ = crate::leanh::lean_ctor_get(v___x_1732_, 3);
                    v_traceState_1737_ = crate::leanh::lean_ctor_get(v___x_1732_, 4);
                    v_messages_1738_ = crate::leanh::lean_ctor_get(v___x_1732_, 6);
                    v_infoState_1739_ = crate::leanh::lean_ctor_get(v___x_1732_, 7);
                    v_snapshotTasks_1740_ = crate::leanh::lean_ctor_get(v___x_1732_, 8);
                    v_isSharedCheck_1749_ = (!crate::leanh::lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1749_ == 0 {
                        v_unused_1750_ = crate::leanh::lean_ctor_get(v___x_1732_, 5);
                        crate::leanh::lean_dec(v_unused_1750_);
                        v___x_1742_ = v___x_1732_;
                        v_isShared_1743_ = v_isSharedCheck_1749_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_1740_);
                        crate::leanh::lean_inc(v_infoState_1739_);
                        crate::leanh::lean_inc(v_messages_1738_);
                        crate::leanh::lean_inc(v_traceState_1737_);
                        crate::leanh::lean_inc(v_auxDeclNGen_1736_);
                        crate::leanh::lean_inc(v_ngen_1735_);
                        crate::leanh::lean_inc(v_nextMacroScope_1734_);
                        crate::leanh::lean_inc(v_env_1733_);
                        crate::leanh::lean_dec(v___x_1732_);
                        v___x_1742_ = crate::leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1749_;
                        state = 15;
                        continue;
                    }
                } else {
                    v___y_1707_ = v___y_1726_;
                    v___y_1708_ = v___y_1729_;
                    v___y_1709_ = v___y_1730_;
                    v___y_1710_ = v___y_1727_;
                    v___y_1711_ = v___y_1728_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_1744_ = l_Lean_Kernel_enableDiag(v_env_1733_, v___y_1729_);
                if v_isShared_1743_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1742_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1744_);
                    v___x_1746_ = v___x_1742_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1748_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_nextMacroScope_1734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_ngen_1735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_auxDeclNGen_1736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 4, v_traceState_1737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 6, v_messages_1738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 7, v_infoState_1739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 8, v_snapshotTasks_1740_);
                    v___x_1746_ = v_reuseFailAlloc_1748_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1747_ = lean_st_ref_set(v___y_1728_, v___x_1746_);
                v___y_1707_ = v___y_1726_;
                v___y_1708_ = v___y_1729_;
                v___y_1709_ = v___y_1730_;
                v___y_1710_ = v___y_1727_;
                v___y_1711_ = v___y_1728_;
                state = 13;
                continue;
            }
            17 => {
                v___x_1760_ = lean_st_ref_get(v___y_1759_);
                v_fileName_1761_ = crate::leanh::lean_ctor_get(v___y_1758_, 0);
                v_fileMap_1762_ = crate::leanh::lean_ctor_get(v___y_1758_, 1);
                v_currRecDepth_1763_ = crate::leanh::lean_ctor_get(v___y_1758_, 3);
                v_ref_1764_ = crate::leanh::lean_ctor_get(v___y_1758_, 5);
                v_currNamespace_1765_ = crate::leanh::lean_ctor_get(v___y_1758_, 6);
                v_openDecls_1766_ = crate::leanh::lean_ctor_get(v___y_1758_, 7);
                v_initHeartbeats_1767_ = crate::leanh::lean_ctor_get(v___y_1758_, 8);
                v_maxHeartbeats_1768_ = crate::leanh::lean_ctor_get(v___y_1758_, 9);
                v_quotContext_1769_ = crate::leanh::lean_ctor_get(v___y_1758_, 10);
                v_currMacroScope_1770_ = crate::leanh::lean_ctor_get(v___y_1758_, 11);
                v_cancelTk_x3f_1771_ = crate::leanh::lean_ctor_get(v___y_1758_, 12);
                v_suppressElabErrors_1772_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1758_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1773_ = crate::leanh::lean_ctor_get(v___y_1758_, 13);
                v_isSharedCheck_1786_ = (!crate::leanh::lean_is_exclusive(v___y_1758_)) as u8;
                if v_isSharedCheck_1786_ == 0 {
                    v_unused_1787_ = crate::leanh::lean_ctor_get(v___y_1758_, 4);
                    crate::leanh::lean_dec(v_unused_1787_);
                    v_unused_1788_ = crate::leanh::lean_ctor_get(v___y_1758_, 2);
                    crate::leanh::lean_dec(v_unused_1788_);
                    v___x_1775_ = v___y_1758_;
                    v_isShared_1776_ = v_isSharedCheck_1786_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inheritedTraceOptions_1773_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_1771_);
                    crate::leanh::lean_inc(v_currMacroScope_1770_);
                    crate::leanh::lean_inc(v_quotContext_1769_);
                    crate::leanh::lean_inc(v_maxHeartbeats_1768_);
                    crate::leanh::lean_inc(v_initHeartbeats_1767_);
                    crate::leanh::lean_inc(v_openDecls_1766_);
                    crate::leanh::lean_inc(v_currNamespace_1765_);
                    crate::leanh::lean_inc(v_ref_1764_);
                    crate::leanh::lean_inc(v_currRecDepth_1763_);
                    crate::leanh::lean_inc(v_fileMap_1762_);
                    crate::leanh::lean_inc(v_fileName_1761_);
                    crate::leanh::lean_dec(v___y_1758_);
                    v___x_1775_ = crate::leanh::lean_box(0);
                    v_isShared_1776_ = v_isSharedCheck_1786_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_env_1777_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                crate::leanh::lean_inc_ref(v_env_1777_);
                crate::leanh::lean_dec(v___x_1760_);
                v___x_1778_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
                    v___y_1756_,
                    v___y_1757_,
                );
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1773_);
                crate::leanh::lean_inc(v_cancelTk_x3f_1771_);
                crate::leanh::lean_inc(v_currMacroScope_1770_);
                crate::leanh::lean_inc(v_quotContext_1769_);
                crate::leanh::lean_inc(v_maxHeartbeats_1768_);
                crate::leanh::lean_inc(v_initHeartbeats_1767_);
                crate::leanh::lean_inc(v_openDecls_1766_);
                crate::leanh::lean_inc(v_currNamespace_1765_);
                crate::leanh::lean_inc(v_ref_1764_);
                crate::leanh::lean_inc(v_currRecDepth_1763_);
                crate::leanh::lean_inc_ref(v___y_1756_);
                crate::leanh::lean_inc_ref(v_fileMap_1762_);
                crate::leanh::lean_inc_ref(v_fileName_1761_);
                if v_isShared_1776_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1775_, 4, v___x_1778_);
                    crate::leanh::lean_ctor_set(v___x_1775_, 2, v___y_1756_);
                    v___x_1780_ = v___x_1775_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fileName_1761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_fileMap_1762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 2, v___y_1756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_currRecDepth_1763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 4, v___x_1778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_ref_1764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 6, v_currNamespace_1765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 7, v_openDecls_1766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 8, v_initHeartbeats_1767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 9, v_maxHeartbeats_1768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 10, v_quotContext_1769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 11, v_currMacroScope_1770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 12, v_cancelTk_x3f_1771_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1785_,
                        13,
                        v_inheritedTraceOptions_1773_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1785_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1772_,
                    );
                    v___x_1780_ = v_reuseFailAlloc_1785_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1780_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_1755_,
                );
                v___x_1781_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
                v___x_1782_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
                    v___y_1756_,
                    v___x_1781_,
                    v___x_1680_,
                );
                v___x_1783_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(
                    v___x_1782_,
                    v___x_1753_,
                );
                v___x_1784_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1777_);
                crate::leanh::lean_dec_ref(v_env_1777_);
                if v___x_1784_ == 0 {
                    if v___x_1783_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1780_);
                        v___y_1683_ = v___x_1782_;
                        v___y_1684_ = v___x_1783_;
                        v___y_1685_ = v___y_1757_;
                        v_fileName_1686_ = v_fileName_1761_;
                        v_fileMap_1687_ = v_fileMap_1762_;
                        v_currRecDepth_1688_ = v_currRecDepth_1763_;
                        v_ref_1689_ = v_ref_1764_;
                        v_currNamespace_1690_ = v_currNamespace_1765_;
                        v_openDecls_1691_ = v_openDecls_1766_;
                        v_initHeartbeats_1692_ = v_initHeartbeats_1767_;
                        v_maxHeartbeats_1693_ = v_maxHeartbeats_1768_;
                        v_quotContext_1694_ = v_quotContext_1769_;
                        v_currMacroScope_1695_ = v_currMacroScope_1770_;
                        v_cancelTk_x3f_1696_ = v_cancelTk_x3f_1771_;
                        v_suppressElabErrors_1697_ = v_suppressElabErrors_1772_;
                        v_inheritedTraceOptions_1698_ = v_inheritedTraceOptions_1773_;
                        v___y_1699_ = v___y_1759_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_inheritedTraceOptions_1773_);
                        crate::leanh::lean_dec(v_cancelTk_x3f_1771_);
                        crate::leanh::lean_dec(v_currMacroScope_1770_);
                        crate::leanh::lean_dec(v_quotContext_1769_);
                        crate::leanh::lean_dec(v_maxHeartbeats_1768_);
                        crate::leanh::lean_dec(v_initHeartbeats_1767_);
                        crate::leanh::lean_dec(v_openDecls_1766_);
                        crate::leanh::lean_dec(v_currNamespace_1765_);
                        crate::leanh::lean_dec(v_ref_1764_);
                        crate::leanh::lean_dec(v_currRecDepth_1763_);
                        crate::leanh::lean_dec_ref(v_fileMap_1762_);
                        crate::leanh::lean_dec_ref(v_fileName_1761_);
                        v___y_1726_ = v___x_1782_;
                        v___y_1727_ = v___x_1780_;
                        v___y_1728_ = v___y_1759_;
                        v___y_1729_ = v___x_1783_;
                        v___y_1730_ = v___y_1757_;
                        v___y_1731_ = v___x_1784_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inheritedTraceOptions_1773_);
                    crate::leanh::lean_dec(v_cancelTk_x3f_1771_);
                    crate::leanh::lean_dec(v_currMacroScope_1770_);
                    crate::leanh::lean_dec(v_quotContext_1769_);
                    crate::leanh::lean_dec(v_maxHeartbeats_1768_);
                    crate::leanh::lean_dec(v_initHeartbeats_1767_);
                    crate::leanh::lean_dec(v_openDecls_1766_);
                    crate::leanh::lean_dec(v_currNamespace_1765_);
                    crate::leanh::lean_dec(v_ref_1764_);
                    crate::leanh::lean_dec(v_currRecDepth_1763_);
                    crate::leanh::lean_dec_ref(v_fileMap_1762_);
                    crate::leanh::lean_dec_ref(v_fileName_1761_);
                    v___y_1726_ = v___x_1782_;
                    v___y_1727_ = v___x_1780_;
                    v___y_1728_ = v___y_1759_;
                    v___y_1729_ = v___x_1783_;
                    v___y_1730_ = v___y_1757_;
                    v___y_1731_ = v___x_1783_;
                    state = 14;
                    continue;
                }
            }
            20 => {
                if v___y_1795_ == 0 {
                    v___x_1796_ = lean_st_ref_take(v___y_1793_);
                    v_env_1797_ = crate::leanh::lean_ctor_get(v___x_1796_, 0);
                    v_nextMacroScope_1798_ = crate::leanh::lean_ctor_get(v___x_1796_, 1);
                    v_ngen_1799_ = crate::leanh::lean_ctor_get(v___x_1796_, 2);
                    v_auxDeclNGen_1800_ = crate::leanh::lean_ctor_get(v___x_1796_, 3);
                    v_traceState_1801_ = crate::leanh::lean_ctor_get(v___x_1796_, 4);
                    v_messages_1802_ = crate::leanh::lean_ctor_get(v___x_1796_, 6);
                    v_infoState_1803_ = crate::leanh::lean_ctor_get(v___x_1796_, 7);
                    v_snapshotTasks_1804_ = crate::leanh::lean_ctor_get(v___x_1796_, 8);
                    v_isSharedCheck_1813_ = (!crate::leanh::lean_is_exclusive(v___x_1796_)) as u8;
                    if v_isSharedCheck_1813_ == 0 {
                        v_unused_1814_ = crate::leanh::lean_ctor_get(v___x_1796_, 5);
                        crate::leanh::lean_dec(v_unused_1814_);
                        v___x_1806_ = v___x_1796_;
                        v_isShared_1807_ = v_isSharedCheck_1813_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_1804_);
                        crate::leanh::lean_inc(v_infoState_1803_);
                        crate::leanh::lean_inc(v_messages_1802_);
                        crate::leanh::lean_inc(v_traceState_1801_);
                        crate::leanh::lean_inc(v_auxDeclNGen_1800_);
                        crate::leanh::lean_inc(v_ngen_1799_);
                        crate::leanh::lean_inc(v_nextMacroScope_1798_);
                        crate::leanh::lean_inc(v_env_1797_);
                        crate::leanh::lean_dec(v___x_1796_);
                        v___x_1806_ = crate::leanh::lean_box(0);
                        v_isShared_1807_ = v_isSharedCheck_1813_;
                        state = 21;
                        continue;
                    }
                } else {
                    v___y_1755_ = v___y_1791_;
                    v___y_1756_ = v___y_1792_;
                    v___y_1757_ = v___y_1794_;
                    v___y_1758_ = v___y_1790_;
                    v___y_1759_ = v___y_1793_;
                    state = 17;
                    continue;
                }
            }
            21 => {
                v___x_1808_ = l_Lean_Kernel_enableDiag(v_env_1797_, v___y_1791_);
                if v_isShared_1807_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1806_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v___x_1806_, 0, v___x_1808_);
                    v___x_1810_ = v___x_1806_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_nextMacroScope_1798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_ngen_1799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_auxDeclNGen_1800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_traceState_1801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 6, v_messages_1802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 7, v_infoState_1803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 8, v_snapshotTasks_1804_);
                    v___x_1810_ = v_reuseFailAlloc_1812_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1811_ = lean_st_ref_set(v___y_1793_, v___x_1810_);
                v___y_1755_ = v___y_1791_;
                v___y_1756_ = v___y_1792_;
                v___y_1757_ = v___y_1794_;
                v___y_1758_ = v___y_1790_;
                v___y_1759_ = v___y_1793_;
                state = 17;
                continue;
            }
            23 => {
                v___x_1819_ = lean_st_ref_get(v___y_1818_);
                v_fileName_1820_ = crate::leanh::lean_ctor_get(v___y_1817_, 0);
                v_fileMap_1821_ = crate::leanh::lean_ctor_get(v___y_1817_, 1);
                v_currRecDepth_1822_ = crate::leanh::lean_ctor_get(v___y_1817_, 3);
                v_ref_1823_ = crate::leanh::lean_ctor_get(v___y_1817_, 5);
                v_currNamespace_1824_ = crate::leanh::lean_ctor_get(v___y_1817_, 6);
                v_openDecls_1825_ = crate::leanh::lean_ctor_get(v___y_1817_, 7);
                v_initHeartbeats_1826_ = crate::leanh::lean_ctor_get(v___y_1817_, 8);
                v_maxHeartbeats_1827_ = crate::leanh::lean_ctor_get(v___y_1817_, 9);
                v_quotContext_1828_ = crate::leanh::lean_ctor_get(v___y_1817_, 10);
                v_currMacroScope_1829_ = crate::leanh::lean_ctor_get(v___y_1817_, 11);
                v_cancelTk_x3f_1830_ = crate::leanh::lean_ctor_get(v___y_1817_, 12);
                v_suppressElabErrors_1831_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1817_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1832_ = crate::leanh::lean_ctor_get(v___y_1817_, 13);
                v_isSharedCheck_1846_ = (!crate::leanh::lean_is_exclusive(v___y_1817_)) as u8;
                if v_isSharedCheck_1846_ == 0 {
                    v_unused_1847_ = crate::leanh::lean_ctor_get(v___y_1817_, 4);
                    crate::leanh::lean_dec(v_unused_1847_);
                    v_unused_1848_ = crate::leanh::lean_ctor_get(v___y_1817_, 2);
                    crate::leanh::lean_dec(v_unused_1848_);
                    v___x_1834_ = v___y_1817_;
                    v_isShared_1835_ = v_isSharedCheck_1846_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inheritedTraceOptions_1832_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_1830_);
                    crate::leanh::lean_inc(v_currMacroScope_1829_);
                    crate::leanh::lean_inc(v_quotContext_1828_);
                    crate::leanh::lean_inc(v_maxHeartbeats_1827_);
                    crate::leanh::lean_inc(v_initHeartbeats_1826_);
                    crate::leanh::lean_inc(v_openDecls_1825_);
                    crate::leanh::lean_inc(v_currNamespace_1824_);
                    crate::leanh::lean_inc(v_ref_1823_);
                    crate::leanh::lean_inc(v_currRecDepth_1822_);
                    crate::leanh::lean_inc(v_fileMap_1821_);
                    crate::leanh::lean_inc(v_fileName_1820_);
                    crate::leanh::lean_dec(v___y_1817_);
                    v___x_1834_ = crate::leanh::lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1846_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_env_1836_ = crate::leanh::lean_ctor_get(v___x_1819_, 0);
                crate::leanh::lean_inc_ref(v_env_1836_);
                crate::leanh::lean_dec(v___x_1819_);
                v___x_1837_ = l_Lean_maxRecDepth;
                v___x_1838_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
                    v___x_1752_,
                    v___x_1837_,
                );
                crate::leanh::lean_inc_ref(v___x_1752_);
                if v_isShared_1835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1834_, 4, v___x_1838_);
                    crate::leanh::lean_ctor_set(v___x_1834_, 2, v___x_1752_);
                    v___x_1840_ = v___x_1834_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fileName_1820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_fileMap_1821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 2, v___x_1752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_currRecDepth_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 4, v___x_1838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_ref_1823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_currNamespace_1824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_openDecls_1825_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 8, v_initHeartbeats_1826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_maxHeartbeats_1827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 10, v_quotContext_1828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 11, v_currMacroScope_1829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 12, v_cancelTk_x3f_1830_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1845_,
                        13,
                        v_inheritedTraceOptions_1832_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1845_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1831_,
                    );
                    v___x_1840_ = v_reuseFailAlloc_1845_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1840_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___x_1815_,
                );
                v___x_1841_ = l_Lean_Compiler_compiler_postponeCompile;
                v___x_1842_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
                    v___x_1752_,
                    v___x_1841_,
                    v___x_1681_,
                );
                v___x_1843_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(
                    v___x_1842_,
                    v___x_1753_,
                );
                v___x_1844_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1836_);
                crate::leanh::lean_dec_ref(v_env_1836_);
                if v___x_1844_ == 0 {
                    if v___x_1843_ == 0 {
                        v___y_1755_ = v___x_1843_;
                        v___y_1756_ = v___x_1842_;
                        v___y_1757_ = v___x_1837_;
                        v___y_1758_ = v___x_1840_;
                        v___y_1759_ = v___y_1818_;
                        state = 17;
                        continue;
                    } else {
                        v___y_1790_ = v___x_1840_;
                        v___y_1791_ = v___x_1843_;
                        v___y_1792_ = v___x_1842_;
                        v___y_1793_ = v___y_1818_;
                        v___y_1794_ = v___x_1837_;
                        v___y_1795_ = v___x_1844_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___y_1790_ = v___x_1840_;
                    v___y_1791_ = v___x_1843_;
                    v___y_1792_ = v___x_1842_;
                    v___y_1793_ = v___y_1818_;
                    v___y_1794_ = v___x_1837_;
                    v___y_1795_ = v___x_1843_;
                    state = 20;
                    continue;
                }
            }
            26 => {
                if v___y_1850_ == 0 {
                    v___x_1851_ = lean_st_ref_take(v___y_1595_);
                    v_env_1852_ = crate::leanh::lean_ctor_get(v___x_1851_, 0);
                    v_nextMacroScope_1853_ = crate::leanh::lean_ctor_get(v___x_1851_, 1);
                    v_ngen_1854_ = crate::leanh::lean_ctor_get(v___x_1851_, 2);
                    v_auxDeclNGen_1855_ = crate::leanh::lean_ctor_get(v___x_1851_, 3);
                    v_traceState_1856_ = crate::leanh::lean_ctor_get(v___x_1851_, 4);
                    v_messages_1857_ = crate::leanh::lean_ctor_get(v___x_1851_, 6);
                    v_infoState_1858_ = crate::leanh::lean_ctor_get(v___x_1851_, 7);
                    v_snapshotTasks_1859_ = crate::leanh::lean_ctor_get(v___x_1851_, 8);
                    v_isSharedCheck_1868_ = (!crate::leanh::lean_is_exclusive(v___x_1851_)) as u8;
                    if v_isSharedCheck_1868_ == 0 {
                        v_unused_1869_ = crate::leanh::lean_ctor_get(v___x_1851_, 5);
                        crate::leanh::lean_dec(v_unused_1869_);
                        v___x_1861_ = v___x_1851_;
                        v_isShared_1862_ = v_isSharedCheck_1868_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_1859_);
                        crate::leanh::lean_inc(v_infoState_1858_);
                        crate::leanh::lean_inc(v_messages_1857_);
                        crate::leanh::lean_inc(v_traceState_1856_);
                        crate::leanh::lean_inc(v_auxDeclNGen_1855_);
                        crate::leanh::lean_inc(v_ngen_1854_);
                        crate::leanh::lean_inc(v_nextMacroScope_1853_);
                        crate::leanh::lean_inc(v_env_1852_);
                        crate::leanh::lean_dec(v___x_1851_);
                        v___x_1861_ = crate::leanh::lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1868_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v___y_1594_);
                    v___y_1817_ = v___y_1594_;
                    v___y_1818_ = v___y_1595_;
                    state = 23;
                    continue;
                }
            }
            27 => {
                v___x_1863_ = l_Lean_Kernel_enableDiag(v_env_1852_, v___x_1815_);
                if v_isShared_1862_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1861_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v___x_1861_, 0, v___x_1863_);
                    v___x_1865_ = v___x_1861_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_nextMacroScope_1853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_ngen_1854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_auxDeclNGen_1855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_traceState_1856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 5, v___x_1656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_messages_1857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 7, v_infoState_1858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_snapshotTasks_1859_);
                    v___x_1865_ = v_reuseFailAlloc_1867_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_1866_ = lean_st_ref_set(v___y_1595_, v___x_1865_);
                crate::leanh::lean_inc_ref(v___y_1594_);
                v___y_1817_ = v___y_1594_;
                v___y_1818_ = v___y_1595_;
                state = 23;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_nativeEqTrue___lam__0___boxed(
    mut v___x_1879_: *mut crate::leanh::LeanObject,
    mut v___x_1880_: *mut crate::leanh::LeanObject,
    mut v___x_1881_: *mut crate::leanh::LeanObject,
    mut v_tacticName_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1889_ = l_Lean_Meta_nativeEqTrue___lam__0(
        v___x_1879_,
        v___x_1880_,
        v___x_1881_,
        v_tacticName_1882_,
        v_a_1883_,
        v___y_1884_,
        v___y_1885_,
        v___y_1886_,
        v___y_1887_,
    );
    crate::leanh::lean_dec(v___y_1887_);
    crate::leanh::lean_dec(v___y_1885_);
    crate::leanh::lean_dec_ref(v___y_1884_);
    return v_res_1889_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(
    mut v_stx_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v_fileMap_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1893_ = 0;
                v___x_1894_ = l_Lean_Syntax_getRange_x3f(v_stx_1890_, v___x_1893_);
                if crate::leanh::lean_obj_tag(v___x_1894_) == 1 {
                    v_val_1895_ = crate::leanh::lean_ctor_get(v___x_1894_, 0);
                    v_isSharedCheck_1907_ = (!crate::leanh::lean_is_exclusive(v___x_1894_)) as u8;
                    if v_isSharedCheck_1907_ == 0 {
                        v___x_1897_ = v___x_1894_;
                        v_isShared_1898_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1895_);
                        crate::leanh::lean_dec(v___x_1894_);
                        v___x_1897_ = crate::leanh::lean_box(0);
                        v_isShared_1898_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1894_);
                    v___x_1908_ = crate::leanh::lean_box(0);
                    v___x_1909_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1909_, 0, v___x_1908_);
                    return v___x_1909_;
                }
            }
            1 => {
                v_fileMap_1899_ = crate::leanh::lean_ctor_get(v___y_1891_, 1);
                v_start_1900_ = crate::leanh::lean_ctor_get(v_val_1895_, 0);
                crate::leanh::lean_inc(v_start_1900_);
                v_stop_1901_ = crate::leanh::lean_ctor_get(v_val_1895_, 1);
                crate::leanh::lean_inc(v_stop_1901_);
                crate::leanh::lean_dec(v_val_1895_);
                crate::leanh::lean_inc_ref(v_fileMap_1899_);
                v___x_1902_ = l_Lean_DeclarationRange_ofStringPositions(
                    v_fileMap_1899_,
                    v_start_1900_,
                    v_stop_1901_,
                );
                crate::leanh::lean_dec(v_stop_1901_);
                crate::leanh::lean_dec(v_start_1900_);
                if v_isShared_1898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1897_, 0, v___x_1902_);
                    v___x_1904_ = v___x_1897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1902_);
                    v___x_1904_ = v_reuseFailAlloc_1906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                return v___x_1905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(
    mut v_stx_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_1910_, v___y_1911_);
    crate::leanh::lean_dec_ref(v___y_1911_);
    crate::leanh::lean_dec(v_stx_1910_);
    return v_res_1913_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(
    mut v_declName_1914_: *mut crate::leanh::LeanObject,
    mut v_declRanges_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1945_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut v_unused_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut v_unused_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1919_ = l_Lean_Name_isAnonymous(v_declName_1914_);
                if v___x_1919_ == 0 {
                    v___x_1920_ = lean_st_ref_take(v___y_1917_);
                    v_env_1921_ = crate::leanh::lean_ctor_get(v___x_1920_, 0);
                    v_nextMacroScope_1922_ = crate::leanh::lean_ctor_get(v___x_1920_, 1);
                    v_ngen_1923_ = crate::leanh::lean_ctor_get(v___x_1920_, 2);
                    v_auxDeclNGen_1924_ = crate::leanh::lean_ctor_get(v___x_1920_, 3);
                    v_traceState_1925_ = crate::leanh::lean_ctor_get(v___x_1920_, 4);
                    v_messages_1926_ = crate::leanh::lean_ctor_get(v___x_1920_, 6);
                    v_infoState_1927_ = crate::leanh::lean_ctor_get(v___x_1920_, 7);
                    v_snapshotTasks_1928_ = crate::leanh::lean_ctor_get(v___x_1920_, 8);
                    v_isSharedCheck_1956_ = (!crate::leanh::lean_is_exclusive(v___x_1920_)) as u8;
                    if v_isSharedCheck_1956_ == 0 {
                        v_unused_1957_ = crate::leanh::lean_ctor_get(v___x_1920_, 5);
                        crate::leanh::lean_dec(v_unused_1957_);
                        v___x_1930_ = v___x_1920_;
                        v_isShared_1931_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_1928_);
                        crate::leanh::lean_inc(v_infoState_1927_);
                        crate::leanh::lean_inc(v_messages_1926_);
                        crate::leanh::lean_inc(v_traceState_1925_);
                        crate::leanh::lean_inc(v_auxDeclNGen_1924_);
                        crate::leanh::lean_inc(v_ngen_1923_);
                        crate::leanh::lean_inc(v_nextMacroScope_1922_);
                        crate::leanh::lean_inc(v_env_1921_);
                        crate::leanh::lean_dec(v___x_1920_);
                        v___x_1930_ = crate::leanh::lean_box(0);
                        v_isShared_1931_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_declRanges_1915_);
                    crate::leanh::lean_dec(v_declName_1914_);
                    v___x_1958_ = crate::leanh::lean_box(0);
                    v___x_1959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1958_);
                    return v___x_1959_;
                }
            }
            1 => {
                v___x_1932_ = l_Lean_declRangeExt;
                v___x_1933_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_1932_,
                    v_env_1921_,
                    v_declName_1914_,
                    v_declRanges_1915_,
                );
                v___x_1934_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_1931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1930_, 5, v___x_1934_);
                    crate::leanh::lean_ctor_set(v___x_1930_, 0, v___x_1933_);
                    v___x_1936_ = v___x_1930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1955_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_nextMacroScope_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_ngen_1923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_auxDeclNGen_1924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_traceState_1925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 5, v___x_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_messages_1926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 7, v_infoState_1927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 8, v_snapshotTasks_1928_);
                    v___x_1936_ = v_reuseFailAlloc_1955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1937_ = lean_st_ref_set(v___y_1917_, v___x_1936_);
                v___x_1938_ = lean_st_ref_take(v___y_1916_);
                v_mctx_1939_ = crate::leanh::lean_ctor_get(v___x_1938_, 0);
                v_zetaDeltaFVarIds_1940_ = crate::leanh::lean_ctor_get(v___x_1938_, 2);
                v_postponed_1941_ = crate::leanh::lean_ctor_get(v___x_1938_, 3);
                v_diag_1942_ = crate::leanh::lean_ctor_get(v___x_1938_, 4);
                v_isSharedCheck_1953_ = (!crate::leanh::lean_is_exclusive(v___x_1938_)) as u8;
                if v_isSharedCheck_1953_ == 0 {
                    v_unused_1954_ = crate::leanh::lean_ctor_get(v___x_1938_, 1);
                    crate::leanh::lean_dec(v_unused_1954_);
                    v___x_1944_ = v___x_1938_;
                    v_isShared_1945_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1942_);
                    crate::leanh::lean_inc(v_postponed_1941_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1940_);
                    crate::leanh::lean_inc(v_mctx_1939_);
                    crate::leanh::lean_dec(v___x_1938_);
                    v___x_1944_ = crate::leanh::lean_box(0);
                    v_isShared_1945_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1946_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_1945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1944_, 1, v___x_1946_);
                    v___x_1948_ = v___x_1944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_mctx_1939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1946_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1952_,
                        2,
                        v_zetaDeltaFVarIds_1940_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_postponed_1941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_diag_1942_);
                    v___x_1948_ = v_reuseFailAlloc_1952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1949_ = lean_st_ref_set(v___y_1916_, v___x_1948_);
                v___x_1950_ = crate::leanh::lean_box(0);
                v___x_1951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1951_, 0, v___x_1950_);
                return v___x_1951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(
    mut v_declName_1960_: *mut crate::leanh::LeanObject,
    mut v_declRanges_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1960_, v_declRanges_1961_, v___y_1962_, v___y_1963_);
    crate::leanh::lean_dec(v___y_1963_);
    crate::leanh::lean_dec(v___y_1962_);
    return v_res_1965_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(
    mut v_declName_1966_: *mut crate::leanh::LeanObject,
    mut v_rangeStx_1967_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_val_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1974_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_rangeStx_1967_, v___y_1971_);
                v_a_1975_ = crate::leanh::lean_ctor_get(v___x_1974_, 0);
                v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v___x_1974_)) as u8;
                if v_isSharedCheck_1991_ == 0 {
                    v___x_1977_ = v___x_1974_;
                    v_isShared_1978_ = v_isSharedCheck_1991_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1975_);
                    crate::leanh::lean_dec(v___x_1974_);
                    v___x_1977_ = crate::leanh::lean_box(0);
                    v_isShared_1978_ = v_isSharedCheck_1991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1975_) == 1 {
                    crate::leanh::lean_del_object(v___x_1977_);
                    v_val_1979_ = crate::leanh::lean_ctor_get(v_a_1975_, 0);
                    crate::leanh::lean_inc(v_val_1979_);
                    crate::leanh::lean_dec_ref_known(v_a_1975_, 1);
                    v___x_1980_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_selectionRangeStx_1968_, v___y_1971_);
                    v_a_1981_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
                    crate::leanh::lean_inc(v_a_1981_);
                    crate::leanh::lean_dec_ref(v___x_1980_);
                    if crate::leanh::lean_obj_tag(v_a_1981_) == 0 {
                        crate::leanh::lean_inc(v_val_1979_);
                        v_a_1983_ = v_val_1979_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1986_ = crate::leanh::lean_ctor_get(v_a_1981_, 0);
                        crate::leanh::lean_inc(v_val_1986_);
                        crate::leanh::lean_dec_ref_known(v_a_1981_, 1);
                        v_a_1983_ = v_val_1986_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1975_);
                    crate::leanh::lean_dec(v_declName_1966_);
                    v___x_1987_ = crate::leanh::lean_box(0);
                    if v_isShared_1978_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1977_, 0, v___x_1987_);
                        v___x_1989_ = v___x_1977_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
                        v___x_1989_ = v_reuseFailAlloc_1990_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1984_, 0, v_val_1979_);
                crate::leanh::lean_ctor_set(v___x_1984_, 1, v_a_1983_);
                v___x_1985_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1966_, v___x_1984_, v___y_1970_, v___y_1972_);
                return v___x_1985_;
            }
            3 => {
                return v___x_1989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(
    mut v_declName_1992_: *mut crate::leanh::LeanObject,
    mut v_rangeStx_1993_: *mut crate::leanh::LeanObject,
    mut v_selectionRangeStx_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2000_ =
        l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(
            v_declName_1992_,
            v_rangeStx_1993_,
            v_selectionRangeStx_1994_,
            v___y_1995_,
            v___y_1996_,
            v___y_1997_,
            v___y_1998_,
        );
    crate::leanh::lean_dec(v___y_1998_);
    crate::leanh::lean_dec_ref(v___y_1997_);
    crate::leanh::lean_dec(v___y_1996_);
    crate::leanh::lean_dec_ref(v___y_1995_);
    crate::leanh::lean_dec(v_selectionRangeStx_1994_);
    crate::leanh::lean_dec(v_rangeStx_1993_);
    return v_res_2000_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(
    mut v_a_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2001_) == 0 {
                    v___x_2003_ = l_List_reverse___redArg(v_a_2002_);
                    return v___x_2003_;
                } else {
                    v_head_2004_ = crate::leanh::lean_ctor_get(v_a_2001_, 0);
                    v_tail_2005_ = crate::leanh::lean_ctor_get(v_a_2001_, 1);
                    v_isSharedCheck_2014_ = (!crate::leanh::lean_is_exclusive(v_a_2001_)) as u8;
                    if v_isSharedCheck_2014_ == 0 {
                        v___x_2007_ = v_a_2001_;
                        v_isShared_2008_ = v_isSharedCheck_2014_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2005_);
                        crate::leanh::lean_inc(v_head_2004_);
                        crate::leanh::lean_dec(v_a_2001_);
                        v___x_2007_ = crate::leanh::lean_box(0);
                        v_isShared_2008_ = v_isSharedCheck_2014_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2009_ = l_Lean_mkLevelParam(v_head_2004_);
                if v_isShared_2008_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2007_, 1, v_a_2002_);
                    crate::leanh::lean_ctor_set(v___x_2007_, 0, v___x_2009_);
                    v___x_2011_ = v___x_2007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_a_2002_);
                    v___x_2011_ = v_reuseFailAlloc_2013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2001_ = v_tail_2005_;
                v_a_2002_ = v___x_2011_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(
    mut v_env_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_unused_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_unused_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2019_ = lean_st_ref_take(v___y_2017_);
                v_nextMacroScope_2020_ = crate::leanh::lean_ctor_get(v___x_2019_, 1);
                v_ngen_2021_ = crate::leanh::lean_ctor_get(v___x_2019_, 2);
                v_auxDeclNGen_2022_ = crate::leanh::lean_ctor_get(v___x_2019_, 3);
                v_traceState_2023_ = crate::leanh::lean_ctor_get(v___x_2019_, 4);
                v_messages_2024_ = crate::leanh::lean_ctor_get(v___x_2019_, 6);
                v_infoState_2025_ = crate::leanh::lean_ctor_get(v___x_2019_, 7);
                v_snapshotTasks_2026_ = crate::leanh::lean_ctor_get(v___x_2019_, 8);
                v_isSharedCheck_2052_ = (!crate::leanh::lean_is_exclusive(v___x_2019_)) as u8;
                if v_isSharedCheck_2052_ == 0 {
                    v_unused_2053_ = crate::leanh::lean_ctor_get(v___x_2019_, 5);
                    crate::leanh::lean_dec(v_unused_2053_);
                    v_unused_2054_ = crate::leanh::lean_ctor_get(v___x_2019_, 0);
                    crate::leanh::lean_dec(v_unused_2054_);
                    v___x_2028_ = v___x_2019_;
                    v_isShared_2029_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2026_);
                    crate::leanh::lean_inc(v_infoState_2025_);
                    crate::leanh::lean_inc(v_messages_2024_);
                    crate::leanh::lean_inc(v_traceState_2023_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2022_);
                    crate::leanh::lean_inc(v_ngen_2021_);
                    crate::leanh::lean_inc(v_nextMacroScope_2020_);
                    crate::leanh::lean_dec(v___x_2019_);
                    v___x_2028_ = crate::leanh::lean_box(0);
                    v_isShared_2029_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2030_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_2029_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2028_, 5, v___x_2030_);
                    crate::leanh::lean_ctor_set(v___x_2028_, 0, v_env_2015_);
                    v___x_2032_ = v___x_2028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_env_2015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_nextMacroScope_2020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_ngen_2021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_auxDeclNGen_2022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_traceState_2023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 5, v___x_2030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 6, v_messages_2024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 7, v_infoState_2025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 8, v_snapshotTasks_2026_);
                    v___x_2032_ = v_reuseFailAlloc_2051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2033_ = lean_st_ref_set(v___y_2017_, v___x_2032_);
                v___x_2034_ = lean_st_ref_take(v___y_2016_);
                v_mctx_2035_ = crate::leanh::lean_ctor_get(v___x_2034_, 0);
                v_zetaDeltaFVarIds_2036_ = crate::leanh::lean_ctor_get(v___x_2034_, 2);
                v_postponed_2037_ = crate::leanh::lean_ctor_get(v___x_2034_, 3);
                v_diag_2038_ = crate::leanh::lean_ctor_get(v___x_2034_, 4);
                v_isSharedCheck_2049_ = (!crate::leanh::lean_is_exclusive(v___x_2034_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v_unused_2050_ = crate::leanh::lean_ctor_get(v___x_2034_, 1);
                    crate::leanh::lean_dec(v_unused_2050_);
                    v___x_2040_ = v___x_2034_;
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2038_);
                    crate::leanh::lean_inc(v_postponed_2037_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2036_);
                    crate::leanh::lean_inc(v_mctx_2035_);
                    crate::leanh::lean_dec(v___x_2034_);
                    v___x_2040_ = crate::leanh::lean_box(0);
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2042_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_2041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2040_, 1, v___x_2042_);
                    v___x_2044_ = v___x_2040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_mctx_2035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2042_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2048_,
                        2,
                        v_zetaDeltaFVarIds_2036_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_postponed_2037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_diag_2038_);
                    v___x_2044_ = v_reuseFailAlloc_2048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2045_ = lean_st_ref_set(v___y_2016_, v___x_2044_);
                v___x_2046_ = crate::leanh::lean_box(0);
                v___x_2047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                return v___x_2047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(
    mut v_env_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2055_, v___y_2056_, v___y_2057_);
    crate::leanh::lean_dec(v___y_2057_);
    crate::leanh::lean_dec(v___y_2056_);
    return v_res_2059_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
    mut v_env_2060_: *mut crate::leanh::LeanObject,
    mut v_x_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
    mut v___y_2063_: *mut crate::leanh::LeanObject,
    mut v___y_2064_: *mut crate::leanh::LeanObject,
    mut v___y_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2074_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v_unused_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_unused_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2067_ = lean_st_ref_get(v___y_2065_);
                v_env_2068_ = crate::leanh::lean_ctor_get(v___x_2067_, 0);
                crate::leanh::lean_inc_ref(v_env_2068_);
                crate::leanh::lean_dec(v___x_2067_);
                v___x_2080_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2060_, v___y_2063_, v___y_2065_);
                crate::leanh::lean_dec_ref(v___x_2080_);
                crate::leanh::lean_inc(v___y_2065_);
                crate::leanh::lean_inc_ref(v___y_2064_);
                crate::leanh::lean_inc(v___y_2063_);
                crate::leanh::lean_inc_ref(v___y_2062_);
                v___x_2081_ = crate::leanh::lean_apply_5(
                    v_x_2061_,
                    v___y_2062_,
                    v___y_2063_,
                    v___y_2064_,
                    v___y_2065_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2081_) == 0 {
                    v_a_2082_ = crate::leanh::lean_ctor_get(v___x_2081_, 0);
                    crate::leanh::lean_inc(v_a_2082_);
                    crate::leanh::lean_dec_ref_known(v___x_2081_, 1);
                    v___x_2083_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2068_, v___y_2063_, v___y_2065_);
                    v_isSharedCheck_2090_ = (!crate::leanh::lean_is_exclusive(v___x_2083_)) as u8;
                    if v_isSharedCheck_2090_ == 0 {
                        v_unused_2091_ = crate::leanh::lean_ctor_get(v___x_2083_, 0);
                        crate::leanh::lean_dec(v_unused_2091_);
                        v___x_2085_ = v___x_2083_;
                        v_isShared_2086_ = v_isSharedCheck_2090_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2083_);
                        v___x_2085_ = crate::leanh::lean_box(0);
                        v_isShared_2086_ = v_isSharedCheck_2090_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2092_ = crate::leanh::lean_ctor_get(v___x_2081_, 0);
                    crate::leanh::lean_inc(v_a_2092_);
                    crate::leanh::lean_dec_ref_known(v___x_2081_, 1);
                    v_a_2070_ = v_a_2092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2071_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2068_, v___y_2063_, v___y_2065_);
                v_isSharedCheck_2078_ = (!crate::leanh::lean_is_exclusive(v___x_2071_)) as u8;
                if v_isSharedCheck_2078_ == 0 {
                    v_unused_2079_ = crate::leanh::lean_ctor_get(v___x_2071_, 0);
                    crate::leanh::lean_dec(v_unused_2079_);
                    v___x_2073_ = v___x_2071_;
                    v_isShared_2074_ = v_isSharedCheck_2078_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2071_);
                    v___x_2073_ = crate::leanh::lean_box(0);
                    v_isShared_2074_ = v_isSharedCheck_2078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2074_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2073_, 1);
                    crate::leanh::lean_ctor_set(v___x_2073_, 0, v_a_2070_);
                    v___x_2076_ = v___x_2073_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2070_);
                    v___x_2076_ = v_reuseFailAlloc_2077_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2076_;
            }
            4 => {
                if v_isShared_2086_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2085_, 0, v_a_2082_);
                    v___x_2088_ = v___x_2085_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2082_);
                    v___x_2088_ = v_reuseFailAlloc_2089_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg___boxed(
    mut v_env_2093_: *mut crate::leanh::LeanObject,
    mut v_x_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
        v_env_2093_,
        v_x_2094_,
        v___y_2095_,
        v___y_2096_,
        v___y_2097_,
        v___y_2098_,
    );
    crate::leanh::lean_dec(v___y_2098_);
    crate::leanh::lean_dec_ref(v___y_2097_);
    crate::leanh::lean_dec(v___y_2096_);
    crate::leanh::lean_dec_ref(v___y_2095_);
    return v_res_2100_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = crate::leanh::lean_box(0);
    v___x_2102_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2103_ = lean_mk_array(v___x_2102_, v___x_2101_);
    return v___x_2103_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__0_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__0,
    );
    v___x_2105_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2105_);
    crate::leanh::lean_ctor_set(v___x_2106_, 1, v___x_2104_);
    return v___x_2106_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_Meta_nativeEqTrue___closed__2;
    v___x_2110_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__1_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__1,
    );
    v___x_2111_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2111_, 0, v___x_2110_);
    crate::leanh::lean_ctor_set(v___x_2111_, 1, v___x_2110_);
    crate::leanh::lean_ctor_set(v___x_2111_, 2, v___x_2109_);
    return v___x_2111_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2125_ = l_Lean_Level_ofNat(v___x_2124_);
    return v___x_2125_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = crate::leanh::lean_box(0);
    v___x_2127_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__12_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__12,
    );
    v___x_2128_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2127_);
    crate::leanh::lean_ctor_set(v___x_2128_, 1, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2129_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__13_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__13,
    );
    v___x_2130_ = l_Lean_Meta_nativeEqTrue___closed__11;
    v___x_2131_ = l_Lean_mkConst(v___x_2130_, v___x_2129_);
    return v___x_2131_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = crate::leanh::lean_box(0);
    v___x_2133_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__7;
    v___x_2134_ = l_Lean_mkConst(v___x_2133_, v___x_2132_);
    return v___x_2134_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = crate::leanh::lean_box(0);
    v___x_2140_ = l_Lean_Meta_nativeEqTrue___closed__17;
    v___x_2141_ = l_Lean_mkConst(v___x_2140_, v___x_2139_);
    return v___x_2141_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_Meta_nativeEqTrue___closed__19;
    v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = l_Lean_Meta_nativeEqTrue___closed__21;
    v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn l_Lean_Meta_nativeEqTrue(
    mut v_tacticName_2148_: *mut crate::leanh::LeanObject,
    mut v_e_2149_: *mut crate::leanh::LeanObject,
    mut v_axiomDeclRange_x3f_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v_env_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v___x_2192_: u8 = 0;
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_a_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_reuseFailAlloc_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut v_unused_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2164_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
                        v_e_2149_, v_a_2152_,
                    );
                v_a_2165_ = crate::leanh::lean_ctor_get(v___x_2164_, 0);
                crate::leanh::lean_inc(v_a_2165_);
                crate::leanh::lean_dec_ref(v___x_2164_);
                v___x_2271_ = l_Lean_Expr_hasFVar(v_a_2165_);
                if v___x_2271_ == 0 {
                    v___y_2250_ = v_a_2151_;
                    v___y_2251_ = v_a_2152_;
                    v___y_2252_ = v_a_2153_;
                    v___y_2253_ = v_a_2154_;
                    state = 15;
                    continue;
                } else {
                    v___x_2272_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_2273_ = l_Lean_MessageData_ofName(v_tacticName_2148_);
                    v___x_2274_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2274_, 0, v___x_2272_);
                    crate::leanh::lean_ctor_set(v___x_2274_, 1, v___x_2273_);
                    v___x_2275_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__22),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__22_once),
                        _init_l_Lean_Meta_nativeEqTrue___closed__22,
                    );
                    v___x_2276_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2274_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                    v___x_2277_ = l_Lean_indentExpr(v_a_2165_);
                    v___x_2278_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2276_);
                    crate::leanh::lean_ctor_set(v___x_2278_, 1, v___x_2277_);
                    v___x_2279_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2278_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
                    v_a_2280_ = crate::leanh::lean_ctor_get(v___x_2279_, 0);
                    v_isSharedCheck_2287_ = (!crate::leanh::lean_is_exclusive(v___x_2279_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2282_ = v___x_2279_;
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2280_);
                        crate::leanh::lean_dec(v___x_2279_);
                        v___x_2282_ = crate::leanh::lean_box(0);
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2159_ = crate::leanh::lean_box(0);
                v___x_2160_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(
                    v___y_2158_,
                    v___x_2159_,
                );
                v___x_2161_ = l_Lean_mkConst(v___y_2157_, v___x_2160_);
                v___x_2162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2162_, 0, v___x_2161_);
                v___x_2163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2163_, 0, v___x_2162_);
                return v___x_2163_;
            }
            2 => {
                v___x_2171_ = lean_st_ref_get(v___y_2170_);
                v___x_2172_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__3_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__3,
                );
                crate::leanh::lean_inc(v_a_2165_);
                v___x_2173_ = l_Lean_collectLevelParams(v___x_2172_, v_a_2165_);
                v_params_2174_ = crate::leanh::lean_ctor_get(v___x_2173_, 2);
                v_isSharedCheck_2246_ = (!crate::leanh::lean_is_exclusive(v___x_2173_)) as u8;
                if v_isSharedCheck_2246_ == 0 {
                    v_unused_2247_ = crate::leanh::lean_ctor_get(v___x_2173_, 1);
                    crate::leanh::lean_dec(v_unused_2247_);
                    v_unused_2248_ = crate::leanh::lean_ctor_get(v___x_2173_, 0);
                    crate::leanh::lean_dec(v_unused_2248_);
                    v___x_2176_ = v___x_2173_;
                    v_isShared_2177_ = v_isSharedCheck_2246_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_2174_);
                    crate::leanh::lean_dec(v___x_2173_);
                    v___x_2176_ = crate::leanh::lean_box(0);
                    v_isShared_2177_ = v_isSharedCheck_2246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_env_2178_ = crate::leanh::lean_ctor_get(v___x_2171_, 0);
                crate::leanh::lean_inc_ref(v_env_2178_);
                crate::leanh::lean_dec(v___x_2171_);
                v___x_2179_ = crate::leanh::lean_box(0);
                v___x_2180_ = lean_array_to_list(v_params_2174_);
                v___x_2181_ = l_Lean_Meta_nativeEqTrue___closed__5;
                crate::leanh::lean_inc(v_tacticName_2148_);
                v___x_2182_ = l_Lean_Name_append(v___x_2181_, v_tacticName_2148_);
                v___x_2183_ = l_Lean_Meta_nativeEqTrue___closed__7;
                crate::leanh::lean_inc(v___x_2182_);
                v___x_2184_ = l_Lean_Name_append(v___x_2182_, v___x_2183_);
                crate::leanh::lean_inc(v_a_2165_);
                crate::leanh::lean_inc(v___x_2180_);
                v___f_2185_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_nativeEqTrue___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_2185_, 0, v___x_2184_);
                crate::leanh::lean_closure_set(v___f_2185_, 1, v___x_2180_);
                crate::leanh::lean_closure_set(v___f_2185_, 2, v___x_2179_);
                crate::leanh::lean_closure_set(v___f_2185_, 3, v_tacticName_2148_);
                crate::leanh::lean_closure_set(v___f_2185_, 4, v_a_2165_);
                v___x_2186_ = l_Lean_Environment_unlockAsync(v_env_2178_);
                v___x_2187_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
                    v___x_2186_,
                    v___f_2185_,
                    v___y_2167_,
                    v___y_2168_,
                    v___y_2169_,
                    v___y_2170_,
                );
                if crate::leanh::lean_obj_tag(v___x_2187_) == 0 {
                    v_a_2188_ = crate::leanh::lean_ctor_get(v___x_2187_, 0);
                    v_isSharedCheck_2237_ = (!crate::leanh::lean_is_exclusive(v___x_2187_)) as u8;
                    if v_isSharedCheck_2237_ == 0 {
                        v___x_2190_ = v___x_2187_;
                        v_isShared_2191_ = v_isSharedCheck_2237_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2188_);
                        crate::leanh::lean_dec(v___x_2187_);
                        v___x_2190_ = crate::leanh::lean_box(0);
                        v_isShared_2191_ = v_isSharedCheck_2237_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2182_);
                    crate::leanh::lean_dec(v___x_2180_);
                    crate::leanh::lean_del_object(v___x_2176_);
                    crate::leanh::lean_dec(v_a_2165_);
                    v_a_2238_ = crate::leanh::lean_ctor_get(v___x_2187_, 0);
                    v_isSharedCheck_2245_ = (!crate::leanh::lean_is_exclusive(v___x_2187_)) as u8;
                    if v_isSharedCheck_2245_ == 0 {
                        v___x_2240_ = v___x_2187_;
                        v_isShared_2241_ = v_isSharedCheck_2245_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2238_);
                        crate::leanh::lean_dec(v___x_2187_);
                        v___x_2240_ = crate::leanh::lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2245_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2192_ = (crate::leanh::lean_unbox(v_a_2188_) as u8);
                crate::leanh::lean_dec(v_a_2188_);
                if v___x_2192_ == 0 {
                    crate::leanh::lean_dec(v___x_2182_);
                    crate::leanh::lean_dec(v___x_2180_);
                    crate::leanh::lean_del_object(v___x_2176_);
                    crate::leanh::lean_dec(v_a_2165_);
                    v___x_2193_ = crate::leanh::lean_box(1);
                    if v_isShared_2191_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2190_, 0, v___x_2193_);
                        v___x_2195_ = v___x_2190_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2196_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
                        v___x_2195_ = v_reuseFailAlloc_2196_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2190_);
                    v___x_2197_ = l_Lean_Meta_nativeEqTrue___closed__9;
                    v___x_2198_ = l_Lean_Name_append(v___x_2182_, v___x_2197_);
                    v___x_2199_ =
                        l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
                            v___x_2198_,
                            v___y_2170_,
                        );
                    v_a_2200_ = crate::leanh::lean_ctor_get(v___x_2199_, 0);
                    v_isSharedCheck_2236_ = (!crate::leanh::lean_is_exclusive(v___x_2199_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2202_ = v___x_2199_;
                        v_isShared_2203_ = v_isSharedCheck_2236_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2200_);
                        crate::leanh::lean_dec(v___x_2199_);
                        v___x_2202_ = crate::leanh::lean_box(0);
                        v_isShared_2203_ = v_isSharedCheck_2236_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2195_;
            }
            6 => {
                v___x_2204_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__14_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__14,
                );
                v___x_2205_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__15_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__15,
                );
                v___x_2206_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__18_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__18,
                );
                v___x_2207_ = l_Lean_mkApp3(v___x_2204_, v___x_2205_, v_a_2165_, v___x_2206_);
                crate::leanh::lean_inc(v___x_2180_);
                crate::leanh::lean_inc(v_a_2200_);
                if v_isShared_2177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2176_, 2, v___x_2207_);
                    crate::leanh::lean_ctor_set(v___x_2176_, 1, v___x_2180_);
                    crate::leanh::lean_ctor_set(v___x_2176_, 0, v_a_2200_);
                    v___x_2209_ = v___x_2176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 2, v___x_2207_);
                    v___x_2209_ = v_reuseFailAlloc_2235_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2210_ = 0;
                v___x_2211_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2211_, 0, v___x_2209_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2211_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2210_,
                );
                if v_isShared_2203_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2202_, 0, v___x_2211_);
                    v___x_2213_ = v___x_2202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2211_);
                    v___x_2213_ = v_reuseFailAlloc_2234_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2214_ = l_Lean_addDecl(v___x_2213_, v___x_2210_, v___y_2169_, v___y_2170_);
                if crate::leanh::lean_obj_tag(v___x_2214_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2214_, 1);
                    if crate::leanh::lean_obj_tag(v_axiomDeclRange_x3f_2150_) == 1 {
                        v_val_2215_ = crate::leanh::lean_ctor_get(v_axiomDeclRange_x3f_2150_, 0);
                        v___x_2216_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_a_2200_);
                        v___x_2217_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_a_2200_, v_val_2215_, v___x_2216_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
                        if crate::leanh::lean_obj_tag(v___x_2217_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2217_, 1);
                            v___y_2157_ = v_a_2200_;
                            v___y_2158_ = v___x_2180_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2200_);
                            crate::leanh::lean_dec(v___x_2180_);
                            v_a_2218_ = crate::leanh::lean_ctor_get(v___x_2217_, 0);
                            v_isSharedCheck_2225_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2217_)) as u8;
                            if v_isSharedCheck_2225_ == 0 {
                                v___x_2220_ = v___x_2217_;
                                v_isShared_2221_ = v_isSharedCheck_2225_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2218_);
                                crate::leanh::lean_dec(v___x_2217_);
                                v___x_2220_ = crate::leanh::lean_box(0);
                                v_isShared_2221_ = v_isSharedCheck_2225_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        v___y_2157_ = v_a_2200_;
                        v___y_2158_ = v___x_2180_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2200_);
                    crate::leanh::lean_dec(v___x_2180_);
                    v_a_2226_ = crate::leanh::lean_ctor_get(v___x_2214_, 0);
                    v_isSharedCheck_2233_ = (!crate::leanh::lean_is_exclusive(v___x_2214_)) as u8;
                    if v_isSharedCheck_2233_ == 0 {
                        v___x_2228_ = v___x_2214_;
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2226_);
                        crate::leanh::lean_dec(v___x_2214_);
                        v___x_2228_ = crate::leanh::lean_box(0);
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2221_ == 0 {
                    v___x_2223_ = v___x_2220_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2223_;
            }
            11 => {
                if v_isShared_2229_ == 0 {
                    v___x_2231_ = v___x_2228_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2231_;
            }
            13 => {
                if v_isShared_2241_ == 0 {
                    v___x_2243_ = v___x_2240_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
                    v___x_2243_ = v_reuseFailAlloc_2244_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2243_;
            }
            15 => {
                v___x_2254_ = l_Lean_Expr_hasMVar(v_a_2165_);
                if v___x_2254_ == 0 {
                    v___y_2167_ = v___y_2250_;
                    v___y_2168_ = v___y_2251_;
                    v___y_2169_ = v___y_2252_;
                    v___y_2170_ = v___y_2253_;
                    state = 2;
                    continue;
                } else {
                    v___x_2255_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_2256_ = l_Lean_MessageData_ofName(v_tacticName_2148_);
                    v___x_2257_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2255_);
                    crate::leanh::lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                    v___x_2258_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__20),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__20_once),
                        _init_l_Lean_Meta_nativeEqTrue___closed__20,
                    );
                    v___x_2259_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2259_, 0, v___x_2257_);
                    crate::leanh::lean_ctor_set(v___x_2259_, 1, v___x_2258_);
                    v___x_2260_ = l_Lean_indentExpr(v_a_2165_);
                    v___x_2261_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2259_);
                    crate::leanh::lean_ctor_set(v___x_2261_, 1, v___x_2260_);
                    v___x_2262_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2261_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
                    v_a_2263_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
                    v_isSharedCheck_2270_ = (!crate::leanh::lean_is_exclusive(v___x_2262_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v___x_2265_ = v___x_2262_;
                        v_isShared_2266_ = v_isSharedCheck_2270_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2263_);
                        crate::leanh::lean_dec(v___x_2262_);
                        v___x_2265_ = crate::leanh::lean_box(0);
                        v_isShared_2266_ = v_isSharedCheck_2270_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_2266_ == 0 {
                    v___x_2268_ = v___x_2265_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2268_;
            }
            18 => {
                if v_isShared_2283_ == 0 {
                    v___x_2285_ = v___x_2282_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
                    v___x_2285_ = v_reuseFailAlloc_2286_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_nativeEqTrue___boxed(
    mut v_tacticName_2288_: *mut crate::leanh::LeanObject,
    mut v_e_2289_: *mut crate::leanh::LeanObject,
    mut v_axiomDeclRange_x3f_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
    mut v_a_2292_: *mut crate::leanh::LeanObject,
    mut v_a_2293_: *mut crate::leanh::LeanObject,
    mut v_a_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Lean_Meta_nativeEqTrue(
        v_tacticName_2288_,
        v_e_2289_,
        v_axiomDeclRange_x3f_2290_,
        v_a_2291_,
        v_a_2292_,
        v_a_2293_,
        v_a_2294_,
    );
    crate::leanh::lean_dec(v_a_2294_);
    crate::leanh::lean_dec_ref(v_a_2293_);
    crate::leanh::lean_dec(v_a_2292_);
    crate::leanh::lean_dec_ref(v_a_2291_);
    crate::leanh::lean_dec(v_axiomDeclRange_x3f_2290_);
    return v_res_2296_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(
    mut v_env_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2297_, v___y_2299_, v___y_2301_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(
    mut v_env_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2310_ =
        l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(
            v_env_2304_,
            v___y_2305_,
            v___y_2306_,
            v___y_2307_,
            v___y_2308_,
        );
    crate::leanh::lean_dec(v___y_2308_);
    crate::leanh::lean_dec_ref(v___y_2307_);
    crate::leanh::lean_dec(v___y_2306_);
    crate::leanh::lean_dec_ref(v___y_2305_);
    return v_res_2310_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(
    mut v_00_u03b1_2311_: *mut crate::leanh::LeanObject,
    mut v_env_2312_: *mut crate::leanh::LeanObject,
    mut v_x_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
        v_env_2312_,
        v_x_2313_,
        v___y_2314_,
        v___y_2315_,
        v___y_2316_,
        v___y_2317_,
    );
    return v___x_2319_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(
    mut v_00_u03b1_2320_: *mut crate::leanh::LeanObject,
    mut v_env_2321_: *mut crate::leanh::LeanObject,
    mut v_x_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(
        v_00_u03b1_2320_,
        v_env_2321_,
        v_x_2322_,
        v___y_2323_,
        v___y_2324_,
        v___y_2325_,
        v___y_2326_,
    );
    crate::leanh::lean_dec(v___y_2326_);
    crate::leanh::lean_dec_ref(v___y_2325_);
    crate::leanh::lean_dec(v___y_2324_);
    crate::leanh::lean_dec_ref(v___y_2323_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(
    mut v_stx_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_2329_, v___y_2332_);
    return v___x_2335_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(
    mut v_stx_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2342_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(v_stx_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
    crate::leanh::lean_dec(v___y_2340_);
    crate::leanh::lean_dec_ref(v___y_2339_);
    crate::leanh::lean_dec(v___y_2338_);
    crate::leanh::lean_dec_ref(v___y_2337_);
    crate::leanh::lean_dec(v_stx_2336_);
    return v_res_2342_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(
    mut v_declName_2343_: *mut crate::leanh::LeanObject,
    mut v_declRanges_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2350_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_2343_, v_declRanges_2344_, v___y_2346_, v___y_2348_);
    return v___x_2350_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(
    mut v_declName_2351_: *mut crate::leanh::LeanObject,
    mut v_declRanges_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(v_declName_2351_, v_declRanges_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
    crate::leanh::lean_dec(v___y_2356_);
    crate::leanh::lean_dec_ref(v___y_2355_);
    crate::leanh::lean_dec(v___y_2354_);
    crate::leanh::lean_dec_ref(v___y_2353_);
    return v_res_2358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Native(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Native(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Native(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Native(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Native(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Native(builtin);
}
