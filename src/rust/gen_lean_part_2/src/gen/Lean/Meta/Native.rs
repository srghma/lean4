// Lean compiler output
// Module: Lean.Meta.Native
// Imports: Lean.Meta.Basic Lean.Util.CollectLevelParams Lean.Elab.DeclarationRange Lean.Compiler.Options
use crate::ffi::{
    lean_array_to_list, lean_has_compile_error, lean_mk_array, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take,
};
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
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value: leanh::LeanStringObject<57> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
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
            96, 32, 102, 97, 105, 108, 101, 100, 46, 32, 69, 114, 114, 111, 114, 58, 32, 0,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__4_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__5_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__4_value)
                as *mut leanh::LeanObject,
            12194354677470204327 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__6_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__7_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__6_value)
                as *mut leanh::LeanObject,
            13787886431423481210 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__8_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__9_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__8_value)
                as *mut leanh::LeanObject,
            16160311484268338767 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__10_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__11_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__10_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__16_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__16_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_nativeEqTrue___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__16_value)
                as *mut leanh::LeanObject,
            9255189395584251158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__19_value: leanh::LeanStringObject<63> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__21_value: leanh::LeanStringObject<64> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_nativeEqTrue___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorIdx(
    mut v_x_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1180_) == 0 {
        let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1181_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1181_;
    } else {
        let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1182_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1182_;
    }
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(
    mut v_x_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1184_ = l_Lean_Meta_NativeEqTrueResult_ctorIdx(v_x_1183_);
    leanh::lean_dec(v_x_1183_);
    return v_res_1184_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(
    mut v_t_1185_: *mut leanh::LeanObject,
    mut v_k_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1185_) == 0 {
        let mut v_prf_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_prf_1187_ = leanh::lean_ctor_get(v_t_1185_, 0);
        leanh::lean_inc_ref(v_prf_1187_);
        leanh::lean_dec_ref_known(v_t_1185_, 1);
        v___x_1188_ = leanh::lean_apply_1(v_k_1186_, v_prf_1187_);
        return v___x_1188_;
    } else {
        return v_k_1186_;
    }
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim(
    mut v_motive_1189_: *mut leanh::LeanObject,
    mut v_ctorIdx_1190_: *mut leanh::LeanObject,
    mut v_t_1191_: *mut leanh::LeanObject,
    mut v_h_1192_: *mut leanh::LeanObject,
    mut v_k_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1194_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1191_, v_k_1193_);
    return v___x_1194_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(
    mut v_motive_1195_: *mut leanh::LeanObject,
    mut v_ctorIdx_1196_: *mut leanh::LeanObject,
    mut v_t_1197_: *mut leanh::LeanObject,
    mut v_h_1198_: *mut leanh::LeanObject,
    mut v_k_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ = l_Lean_Meta_NativeEqTrueResult_ctorElim(
        v_motive_1195_,
        v_ctorIdx_1196_,
        v_t_1197_,
        v_h_1198_,
        v_k_1199_,
    );
    leanh::lean_dec(v_ctorIdx_1196_);
    return v_res_1200_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(
    mut v_t_1201_: *mut leanh::LeanObject,
    mut v_success_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1201_, v_success_1202_);
    return v___x_1203_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_success_elim(
    mut v_motive_1204_: *mut leanh::LeanObject,
    mut v_t_1205_: *mut leanh::LeanObject,
    mut v_h_1206_: *mut leanh::LeanObject,
    mut v_success_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1205_, v_success_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(
    mut v_t_1209_: *mut leanh::LeanObject,
    mut v_notTrue_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1209_, v_notTrue_1210_);
    return v___x_1211_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_notTrue_elim(
    mut v_motive_1212_: *mut leanh::LeanObject,
    mut v_t_1213_: *mut leanh::LeanObject,
    mut v_h_1214_: *mut leanh::LeanObject,
    mut v_notTrue_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1213_, v_notTrue_1215_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = leanh::lean_box(0);
    v___x_1218_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_1219_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1219_, 0, v___x_1218_);
    leanh::lean_ctor_set(v___x_1219_, 1, v___x_1217_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0);
    v___x_1222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1222_, 0, v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___boxed(
    mut v___y_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
    return v_res_1224_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(
    mut v_msgData_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
    mut v___y_1228_: *mut leanh::LeanObject,
    mut v___y_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ = lean_st_ref_get(v___y_1229_);
    v_env_1232_ = leanh::lean_ctor_get(v___x_1231_, 0);
    leanh::lean_inc_ref(v_env_1232_);
    leanh::lean_dec(v___x_1231_);
    v___x_1233_ = lean_st_ref_get(v___y_1227_);
    v_mctx_1234_ = leanh::lean_ctor_get(v___x_1233_, 0);
    leanh::lean_inc_ref(v_mctx_1234_);
    leanh::lean_dec(v___x_1233_);
    v_lctx_1235_ = leanh::lean_ctor_get(v___y_1226_, 2);
    v_options_1236_ = leanh::lean_ctor_get(v___y_1228_, 2);
    leanh::lean_inc_ref(v_options_1236_);
    leanh::lean_inc_ref(v_lctx_1235_);
    v___x_1237_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1237_, 0, v_env_1232_);
    leanh::lean_ctor_set(v___x_1237_, 1, v_mctx_1234_);
    leanh::lean_ctor_set(v___x_1237_, 2, v_lctx_1235_);
    leanh::lean_ctor_set(v___x_1237_, 3, v_options_1236_);
    v___x_1238_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    leanh::lean_ctor_set(v___x_1238_, 1, v_msgData_1225_);
    v___x_1239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    return v___x_1239_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
    mut v___y_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
    leanh::lean_dec(v___y_1244_);
    leanh::lean_dec_ref(v___y_1243_);
    leanh::lean_dec(v___y_1242_);
    leanh::lean_dec_ref(v___y_1241_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(
    mut v_msg_1247_: *mut leanh::LeanObject,
    mut v___y_1248_: *mut leanh::LeanObject,
    mut v___y_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
    mut v___y_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1253_ = leanh::lean_ctor_get(v___y_1250_, 5);
                v___x_1254_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
                v_a_1255_ = leanh::lean_ctor_get(v___x_1254_, 0);
                v_isSharedCheck_1263_ = (!leanh::lean_is_exclusive(v___x_1254_)) as u8;
                if v_isSharedCheck_1263_ == 0 {
                    v___x_1257_ = v___x_1254_;
                    v_isShared_1258_ = v_isSharedCheck_1263_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1255_);
                    leanh::lean_dec(v___x_1254_);
                    v___x_1257_ = leanh::lean_box(0);
                    v_isShared_1258_ = v_isSharedCheck_1263_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1253_);
                v___x_1259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1259_, 0, v_ref_1253_);
                leanh::lean_ctor_set(v___x_1259_, 1, v_a_1255_);
                if v_isShared_1258_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1257_, 1);
                    leanh::lean_ctor_set(v___x_1257_, 0, v___x_1259_);
                    v___x_1261_ = v___x_1257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
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
    mut v_msg_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
    mut v___y_1268_: *mut leanh::LeanObject,
    mut v___y_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
    leanh::lean_dec(v___y_1268_);
    leanh::lean_dec_ref(v___y_1267_);
    leanh::lean_dec(v___y_1266_);
    leanh::lean_dec_ref(v___y_1265_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(
    mut v_x_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1283_: u8 = 0;
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1271_) == 0 {
                    v_a_1277_ = leanh::lean_ctor_get(v_x_1271_, 0);
                    leanh::lean_inc(v_a_1277_);
                    leanh::lean_dec_ref_known(v_x_1271_, 1);
                    v___x_1278_ = l_Lean_stringToMessageData(v_a_1277_);
                    v___x_1279_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1278_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
                    return v___x_1279_;
                } else {
                    v_a_1280_ = leanh::lean_ctor_get(v_x_1271_, 0);
                    v_isSharedCheck_1287_ = (!leanh::lean_is_exclusive(v_x_1271_)) as u8;
                    if v_isSharedCheck_1287_ == 0 {
                        v___x_1282_ = v_x_1271_;
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1280_);
                        leanh::lean_dec(v_x_1271_);
                        v___x_1282_ = leanh::lean_box(0);
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1283_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1282_, 0);
                    v___x_1285_ = v___x_1282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
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
    mut v_x_1288_: *mut leanh::LeanObject,
    mut v___y_1289_: *mut leanh::LeanObject,
    mut v___y_1290_: *mut leanh::LeanObject,
    mut v___y_1291_: *mut leanh::LeanObject,
    mut v___y_1292_: *mut leanh::LeanObject,
    mut v___y_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
    leanh::lean_dec(v___y_1292_);
    leanh::lean_dec_ref(v___y_1291_);
    leanh::lean_dec(v___y_1290_);
    leanh::lean_dec_ref(v___y_1289_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(
    mut v_constName_1295_: *mut leanh::LeanObject,
    mut v_checkMeta_1296_: u8,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
    mut v___y_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1302_ = lean_st_ref_get(v___y_1300_);
                v_env_1303_ = leanh::lean_ctor_get(v___x_1302_, 0);
                leanh::lean_inc_ref(v_env_1303_);
                leanh::lean_dec(v___x_1302_);
                leanh::lean_inc(v_constName_1295_);
                v___x_1304_ = lean_has_compile_error(v_env_1303_, v_constName_1295_);
                if v___x_1304_ == 0 {
                    v___x_1305_ = lean_st_ref_get(v___y_1300_);
                    v_env_1306_ = leanh::lean_ctor_get(v___x_1305_, 0);
                    leanh::lean_inc_ref(v_env_1306_);
                    leanh::lean_dec(v___x_1305_);
                    v_options_1307_ = leanh::lean_ctor_get(v___y_1299_, 2);
                    v___x_1308_ = l_Lean_Environment_evalConst___redArg(
                        v_env_1306_,
                        v_options_1307_,
                        v_constName_1295_,
                        v_checkMeta_1296_,
                    );
                    leanh::lean_dec(v_constName_1295_);
                    leanh::lean_dec_ref(v_env_1306_);
                    v___x_1309_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_1308_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
                    return v___x_1309_;
                } else {
                    v___x_1310_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
                    if leanh::lean_obj_tag(v___x_1310_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1310_, 1);
                        v___x_1311_ = lean_st_ref_get(v___y_1300_);
                        v_env_1312_ = leanh::lean_ctor_get(v___x_1311_, 0);
                        leanh::lean_inc_ref(v_env_1312_);
                        leanh::lean_dec(v___x_1311_);
                        v_options_1313_ = leanh::lean_ctor_get(v___y_1299_, 2);
                        v___x_1314_ = l_Lean_Environment_evalConst___redArg(
                            v_env_1312_,
                            v_options_1313_,
                            v_constName_1295_,
                            v_checkMeta_1296_,
                        );
                        leanh::lean_dec(v_constName_1295_);
                        leanh::lean_dec_ref(v_env_1312_);
                        v___x_1315_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_1314_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
                        return v___x_1315_;
                    } else {
                        leanh::lean_dec(v_constName_1295_);
                        v_a_1316_ = leanh::lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1323_ =
                            (!leanh::lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1323_ == 0 {
                            v___x_1318_ = v___x_1310_;
                            v_isShared_1319_ = v_isSharedCheck_1323_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1316_);
                            leanh::lean_dec(v___x_1310_);
                            v___x_1318_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
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
    mut v_constName_1324_: *mut leanh::LeanObject,
    mut v_checkMeta_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
    mut v___y_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_1331_: u8 = 0;
    let mut v_res_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1331_ = (leanh::lean_unbox(v_checkMeta_1325_) as u8);
    v_res_1332_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_1324_, v_checkMeta_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
    leanh::lean_dec(v___y_1329_);
    leanh::lean_dec_ref(v___y_1328_);
    leanh::lean_dec(v___y_1327_);
    leanh::lean_dec_ref(v___y_1326_);
    return v_res_1332_;
}
pub unsafe fn l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
    mut v_auxDeclName_1333_: *mut leanh::LeanObject,
    mut v_a_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1339_: u8 = 0;
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = 1;
    v___x_1340_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_auxDeclName_1333_, v___x_1339_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
    return v___x_1340_;
}
pub unsafe fn l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(
    mut v_auxDeclName_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
    mut v_a_1344_: *mut leanh::LeanObject,
    mut v_a_1345_: *mut leanh::LeanObject,
    mut v_a_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1347_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
        v_auxDeclName_1341_,
        v_a_1342_,
        v_a_1343_,
        v_a_1344_,
        v_a_1345_,
    );
    leanh::lean_dec(v_a_1345_);
    leanh::lean_dec_ref(v_a_1344_);
    leanh::lean_dec(v_a_1343_);
    leanh::lean_dec_ref(v_a_1342_);
    return v_res_1347_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(
    mut v_00_u03b1_1348_: *mut leanh::LeanObject,
    mut v___y_1349_: *mut leanh::LeanObject,
    mut v___y_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
    return v___x_1354_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___boxed(
    mut v_00_u03b1_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
    mut v___y_1358_: *mut leanh::LeanObject,
    mut v___y_1359_: *mut leanh::LeanObject,
    mut v___y_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(v_00_u03b1_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
    leanh::lean_dec(v___y_1359_);
    leanh::lean_dec_ref(v___y_1358_);
    leanh::lean_dec(v___y_1357_);
    leanh::lean_dec_ref(v___y_1356_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(
    mut v_00_u03b1_1362_: *mut leanh::LeanObject,
    mut v_constName_1363_: *mut leanh::LeanObject,
    mut v_checkMeta_1364_: u8,
    mut v___y_1365_: *mut leanh::LeanObject,
    mut v___y_1366_: *mut leanh::LeanObject,
    mut v___y_1367_: *mut leanh::LeanObject,
    mut v___y_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_1363_, v_checkMeta_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
    return v___x_1370_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___boxed(
    mut v_00_u03b1_1371_: *mut leanh::LeanObject,
    mut v_constName_1372_: *mut leanh::LeanObject,
    mut v_checkMeta_1373_: *mut leanh::LeanObject,
    mut v___y_1374_: *mut leanh::LeanObject,
    mut v___y_1375_: *mut leanh::LeanObject,
    mut v___y_1376_: *mut leanh::LeanObject,
    mut v___y_1377_: *mut leanh::LeanObject,
    mut v___y_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_1379_: u8 = 0;
    let mut v_res_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1379_ = (leanh::lean_unbox(v_checkMeta_1373_) as u8);
    v_res_1380_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(v_00_u03b1_1371_, v_constName_1372_, v_checkMeta_boxed_1379_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
    leanh::lean_dec(v___y_1377_);
    leanh::lean_dec_ref(v___y_1376_);
    leanh::lean_dec(v___y_1375_);
    leanh::lean_dec_ref(v___y_1374_);
    return v_res_1380_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(
    mut v_00_u03b1_1381_: *mut leanh::LeanObject,
    mut v_x_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
    return v___x_1388_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b1_1389_: *mut leanh::LeanObject,
    mut v_x_1390_: *mut leanh::LeanObject,
    mut v___y_1391_: *mut leanh::LeanObject,
    mut v___y_1392_: *mut leanh::LeanObject,
    mut v___y_1393_: *mut leanh::LeanObject,
    mut v___y_1394_: *mut leanh::LeanObject,
    mut v___y_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(v_00_u03b1_1389_, v_x_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
    leanh::lean_dec(v___y_1394_);
    leanh::lean_dec_ref(v___y_1393_);
    leanh::lean_dec(v___y_1392_);
    leanh::lean_dec_ref(v___y_1391_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1397_: *mut leanh::LeanObject,
    mut v_msg_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
    mut v___y_1401_: *mut leanh::LeanObject,
    mut v___y_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1405_: *mut leanh::LeanObject,
    mut v_msg_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
    mut v___y_1410_: *mut leanh::LeanObject,
    mut v___y_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_1405_, v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
    leanh::lean_dec(v___y_1410_);
    leanh::lean_dec_ref(v___y_1409_);
    leanh::lean_dec(v___y_1408_);
    leanh::lean_dec_ref(v___y_1407_);
    return v_res_1412_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
    mut v_e_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: u8 = 0;
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_unused_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1416_ = l_Lean_Expr_hasMVar(v_e_1413_);
                if v___x_1416_ == 0 {
                    v___x_1417_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1417_, 0, v_e_1413_);
                    return v___x_1417_;
                } else {
                    v___x_1418_ = lean_st_ref_get(v___y_1414_);
                    v_mctx_1419_ = leanh::lean_ctor_get(v___x_1418_, 0);
                    leanh::lean_inc_ref(v_mctx_1419_);
                    leanh::lean_dec(v___x_1418_);
                    v___x_1420_ = l_Lean_instantiateMVarsCore(v_mctx_1419_, v_e_1413_);
                    v_fst_1421_ = leanh::lean_ctor_get(v___x_1420_, 0);
                    leanh::lean_inc(v_fst_1421_);
                    v_snd_1422_ = leanh::lean_ctor_get(v___x_1420_, 1);
                    leanh::lean_inc(v_snd_1422_);
                    leanh::lean_dec_ref(v___x_1420_);
                    v___x_1423_ = lean_st_ref_take(v___y_1414_);
                    v_cache_1424_ = leanh::lean_ctor_get(v___x_1423_, 1);
                    v_zetaDeltaFVarIds_1425_ = leanh::lean_ctor_get(v___x_1423_, 2);
                    v_postponed_1426_ = leanh::lean_ctor_get(v___x_1423_, 3);
                    v_diag_1427_ = leanh::lean_ctor_get(v___x_1423_, 4);
                    v_isSharedCheck_1436_ = (!leanh::lean_is_exclusive(v___x_1423_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v_unused_1437_ = leanh::lean_ctor_get(v___x_1423_, 0);
                        leanh::lean_dec(v_unused_1437_);
                        v___x_1429_ = v___x_1423_;
                        v_isShared_1430_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1427_);
                        leanh::lean_inc(v_postponed_1426_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1425_);
                        leanh::lean_inc(v_cache_1424_);
                        leanh::lean_dec(v___x_1423_);
                        v___x_1429_ = leanh::lean_box(0);
                        v_isShared_1430_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1430_ == 0 {
                    leanh::lean_ctor_set(v___x_1429_, 0, v_snd_1422_);
                    v___x_1432_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_snd_1422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_cache_1424_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1435_,
                        2,
                        v_zetaDeltaFVarIds_1425_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_postponed_1426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_diag_1427_);
                    v___x_1432_ = v_reuseFailAlloc_1435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1433_ = lean_st_ref_set(v___y_1414_, v___x_1432_);
                v___x_1434_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1434_, 0, v_fst_1421_);
                return v___x_1434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(
    mut v_e_1438_: *mut leanh::LeanObject,
    mut v___y_1439_: *mut leanh::LeanObject,
    mut v___y_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
        v_e_1438_,
        v___y_1439_,
    );
    leanh::lean_dec(v___y_1439_);
    return v_res_1441_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(
    mut v_e_1442_: *mut leanh::LeanObject,
    mut v___y_1443_: *mut leanh::LeanObject,
    mut v___y_1444_: *mut leanh::LeanObject,
    mut v___y_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
        v_e_1442_,
        v___y_1444_,
    );
    return v___x_1448_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(
    mut v_e_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(
        v_e_1449_,
        v___y_1450_,
        v___y_1451_,
        v___y_1452_,
        v___y_1453_,
    );
    leanh::lean_dec(v___y_1453_);
    leanh::lean_dec_ref(v___y_1452_);
    leanh::lean_dec(v___y_1451_);
    leanh::lean_dec_ref(v___y_1450_);
    return v_res_1455_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
    mut v_kind_1456_: *mut leanh::LeanObject,
    mut v___y_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut v_unused_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1459_ = lean_st_ref_get(v___y_1457_);
                v_auxDeclNGen_1460_ = leanh::lean_ctor_get(v___x_1459_, 3);
                leanh::lean_inc_ref(v_auxDeclNGen_1460_);
                leanh::lean_dec(v___x_1459_);
                v___x_1461_ = lean_st_ref_get(v___y_1457_);
                v_env_1462_ = leanh::lean_ctor_get(v___x_1461_, 0);
                leanh::lean_inc_ref(v_env_1462_);
                leanh::lean_dec(v___x_1461_);
                v___x_1463_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_1462_,
                    v_auxDeclNGen_1460_,
                    v_kind_1456_,
                );
                v_fst_1464_ = leanh::lean_ctor_get(v___x_1463_, 0);
                leanh::lean_inc(v_fst_1464_);
                v_snd_1465_ = leanh::lean_ctor_get(v___x_1463_, 1);
                leanh::lean_inc(v_snd_1465_);
                leanh::lean_dec_ref(v___x_1463_);
                v___x_1466_ = lean_st_ref_take(v___y_1457_);
                v_env_1467_ = leanh::lean_ctor_get(v___x_1466_, 0);
                v_nextMacroScope_1468_ = leanh::lean_ctor_get(v___x_1466_, 1);
                v_ngen_1469_ = leanh::lean_ctor_get(v___x_1466_, 2);
                v_traceState_1470_ = leanh::lean_ctor_get(v___x_1466_, 4);
                v_cache_1471_ = leanh::lean_ctor_get(v___x_1466_, 5);
                v_messages_1472_ = leanh::lean_ctor_get(v___x_1466_, 6);
                v_infoState_1473_ = leanh::lean_ctor_get(v___x_1466_, 7);
                v_snapshotTasks_1474_ = leanh::lean_ctor_get(v___x_1466_, 8);
                v_isSharedCheck_1483_ = (!leanh::lean_is_exclusive(v___x_1466_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v_unused_1484_ = leanh::lean_ctor_get(v___x_1466_, 3);
                    leanh::lean_dec(v_unused_1484_);
                    v___x_1476_ = v___x_1466_;
                    v_isShared_1477_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1474_);
                    leanh::lean_inc(v_infoState_1473_);
                    leanh::lean_inc(v_messages_1472_);
                    leanh::lean_inc(v_cache_1471_);
                    leanh::lean_inc(v_traceState_1470_);
                    leanh::lean_inc(v_ngen_1469_);
                    leanh::lean_inc(v_nextMacroScope_1468_);
                    leanh::lean_inc(v_env_1467_);
                    leanh::lean_dec(v___x_1466_);
                    v___x_1476_ = leanh::lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1477_ == 0 {
                    leanh::lean_ctor_set(v___x_1476_, 3, v_snd_1465_);
                    v___x_1479_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_env_1467_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_nextMacroScope_1468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_ngen_1469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_snd_1465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_traceState_1470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 5, v_cache_1471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 6, v_messages_1472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 7, v_infoState_1473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 8, v_snapshotTasks_1474_);
                    v___x_1479_ = v_reuseFailAlloc_1482_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1480_ = lean_st_ref_set(v___y_1457_, v___x_1479_);
                v___x_1481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1481_, 0, v_fst_1464_);
                return v___x_1481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(
    mut v_kind_1485_: *mut leanh::LeanObject,
    mut v___y_1486_: *mut leanh::LeanObject,
    mut v___y_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
        v_kind_1485_,
        v___y_1486_,
    );
    leanh::lean_dec(v___y_1486_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(
    mut v_kind_1489_: *mut leanh::LeanObject,
    mut v___y_1490_: *mut leanh::LeanObject,
    mut v___y_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
        v_kind_1489_,
        v___y_1493_,
    );
    return v___x_1495_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(
    mut v_kind_1496_: *mut leanh::LeanObject,
    mut v___y_1497_: *mut leanh::LeanObject,
    mut v___y_1498_: *mut leanh::LeanObject,
    mut v___y_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
    mut v___y_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(
        v_kind_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
        v___y_1500_,
    );
    leanh::lean_dec(v___y_1500_);
    leanh::lean_dec_ref(v___y_1499_);
    leanh::lean_dec(v___y_1498_);
    leanh::lean_dec_ref(v___y_1497_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(
    mut v_opts_1503_: *mut leanh::LeanObject,
    mut v_opt_1504_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1505_ = leanh::lean_ctor_get(v_opt_1504_, 0);
    v_defValue_1506_ = leanh::lean_ctor_get(v_opt_1504_, 1);
    v_map_1507_ = leanh::lean_ctor_get(v_opts_1503_, 0);
    v___x_1508_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1507_,
            v_name_1505_,
        );
    if leanh::lean_obj_tag(v___x_1508_) == 0 {
        let mut v___x_1509_: u8 = 0;
        v___x_1509_ = (leanh::lean_unbox(v_defValue_1506_) as u8);
        return v___x_1509_;
    } else {
        let mut v_val_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1510_ = leanh::lean_ctor_get(v___x_1508_, 0);
        leanh::lean_inc(v_val_1510_);
        leanh::lean_dec_ref_known(v___x_1508_, 1);
        if leanh::lean_obj_tag(v_val_1510_) == 1 {
            let mut v_v_1511_: u8 = 0;
            v_v_1511_ = leanh::lean_ctor_get_uint8(v_val_1510_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1510_, 0);
            return v_v_1511_;
        } else {
            let mut v___x_1512_: u8 = 0;
            leanh::lean_dec(v_val_1510_);
            v___x_1512_ = (leanh::lean_unbox(v_defValue_1506_) as u8);
            return v___x_1512_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(
    mut v_opts_1513_: *mut leanh::LeanObject,
    mut v_opt_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ =
        l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v_opts_1513_, v_opt_1514_);
    leanh::lean_dec_ref(v_opt_1514_);
    leanh::lean_dec_ref(v_opts_1513_);
    v_r_1516_ = leanh::lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
    mut v_opts_1517_: *mut leanh::LeanObject,
    mut v_opt_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1519_ = leanh::lean_ctor_get(v_opt_1518_, 0);
    v_defValue_1520_ = leanh::lean_ctor_get(v_opt_1518_, 1);
    v_map_1521_ = leanh::lean_ctor_get(v_opts_1517_, 0);
    v___x_1522_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1521_,
            v_name_1519_,
        );
    if leanh::lean_obj_tag(v___x_1522_) == 0 {
        leanh::lean_inc(v_defValue_1520_);
        return v_defValue_1520_;
    } else {
        let mut v_val_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1523_ = leanh::lean_ctor_get(v___x_1522_, 0);
        leanh::lean_inc(v_val_1523_);
        leanh::lean_dec_ref_known(v___x_1522_, 1);
        if leanh::lean_obj_tag(v_val_1523_) == 3 {
            let mut v_v_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1524_ = leanh::lean_ctor_get(v_val_1523_, 0);
            leanh::lean_inc(v_v_1524_);
            leanh::lean_dec_ref_known(v_val_1523_, 1);
            return v_v_1524_;
        } else {
            leanh::lean_dec(v_val_1523_);
            leanh::lean_inc(v_defValue_1520_);
            return v_defValue_1520_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(
    mut v_opts_1525_: *mut leanh::LeanObject,
    mut v_opt_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1527_ =
        l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_1525_, v_opt_1526_);
    leanh::lean_dec_ref(v_opt_1526_);
    leanh::lean_dec_ref(v_opts_1525_);
    return v_res_1527_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
    mut v_o_1531_: *mut leanh::LeanObject,
    mut v_k_1532_: *mut leanh::LeanObject,
    mut v_v_1533_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1535_: u8 = 0;
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1534_ = leanh::lean_ctor_get(v_o_1531_, 0);
                v_hasTrace_1535_ = leanh::lean_ctor_get_uint8(
                    v_o_1531_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1549_ = (!leanh::lean_is_exclusive(v_o_1531_)) as u8;
                if v_isSharedCheck_1549_ == 0 {
                    v___x_1537_ = v_o_1531_;
                    v_isShared_1538_ = v_isSharedCheck_1549_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_1534_);
                    leanh::lean_dec(v_o_1531_);
                    v___x_1537_ = leanh::lean_box(0);
                    v_isShared_1538_ = v_isSharedCheck_1549_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1539_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_1539_, 0 as u32, v_v_1533_);
                leanh::lean_inc(v_k_1532_);
                v___x_1540_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1532_, v___x_1539_, v_map_1534_);
                if v_hasTrace_1535_ == 0 {
                    v___x_1541_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1;
                    v___x_1542_ = l_Lean_Name_isPrefixOf(v___x_1541_, v_k_1532_);
                    leanh::lean_dec(v_k_1532_);
                    if v_isShared_1538_ == 0 {
                        leanh::lean_ctor_set(v___x_1537_, 0, v___x_1540_);
                        v___x_1544_ = v___x_1537_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1545_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1540_);
                        v___x_1544_ = v_reuseFailAlloc_1545_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_1532_);
                    if v_isShared_1538_ == 0 {
                        leanh::lean_ctor_set(v___x_1537_, 0, v___x_1540_);
                        v___x_1547_ = v___x_1537_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1548_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1540_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1548_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1535_,
                        );
                        v___x_1547_ = v_reuseFailAlloc_1548_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1544_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_o_1550_: *mut leanh::LeanObject,
    mut v_k_1551_: *mut leanh::LeanObject,
    mut v_v_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1553_: u8 = 0;
    let mut v_res_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1553_ = (leanh::lean_unbox(v_v_1552_) as u8);
    v_res_1554_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
            v_o_1550_,
            v_k_1551_,
            v_v_boxed_1553_,
        );
    return v_res_1554_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
    mut v_opts_1555_: *mut leanh::LeanObject,
    mut v_opt_1556_: *mut leanh::LeanObject,
    mut v_val_1557_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1558_ = leanh::lean_ctor_get(v_opt_1556_, 0);
    leanh::lean_inc(v_name_1558_);
    leanh::lean_dec_ref(v_opt_1556_);
    v___x_1559_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
            v_opts_1555_,
            v_name_1558_,
            v_val_1557_,
        );
    return v___x_1559_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(
    mut v_opts_1560_: *mut leanh::LeanObject,
    mut v_opt_1561_: *mut leanh::LeanObject,
    mut v_val_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_1563_: u8 = 0;
    let mut v_res_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_1563_ = (leanh::lean_unbox(v_val_1562_) as u8);
    v_res_1564_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
        v_opts_1560_,
        v_opt_1561_,
        v_val_boxed_1563_,
    );
    return v_res_1564_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__0;
    v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__2;
    v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
    return v___x_1570_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1572_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__4;
    v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = leanh::lean_box(0);
    v___x_1578_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__7;
    v___x_1579_ = l_Lean_mkConst(v___x_1578_, v___x_1577_);
    return v___x_1579_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1580_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10() -> *mut leanh::LeanObject
{
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9,
    );
    v___x_1582_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1582_, 0, v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11() -> *mut leanh::LeanObject
{
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10,
    );
    v___x_1584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1584_, 0, v___x_1583_);
    leanh::lean_ctor_set(v___x_1584_, 1, v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10,
    );
    v___x_1586_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
    leanh::lean_ctor_set(v___x_1586_, 1, v___x_1585_);
    leanh::lean_ctor_set(v___x_1586_, 2, v___x_1585_);
    leanh::lean_ctor_set(v___x_1586_, 3, v___x_1585_);
    leanh::lean_ctor_set(v___x_1586_, 4, v___x_1585_);
    leanh::lean_ctor_set(v___x_1586_, 5, v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn l_Lean_Meta_nativeEqTrue___lam__0(
    mut v___x_1587_: *mut leanh::LeanObject,
    mut v___x_1588_: *mut leanh::LeanObject,
    mut v___x_1589_: *mut leanh::LeanObject,
    mut v_tacticName_1590_: *mut leanh::LeanObject,
    mut v_a_1591_: *mut leanh::LeanObject,
    mut v___y_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: u8 = 0;
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___y_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: u8 = 0;
    let mut v_a_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v___y_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: u8 = 0;
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: u8 = 0;
    let mut v___y_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: u8 = 0;
    let mut v___y_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1697_: u8 = 0;
    let mut v_inheritedTraceOptions_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: u8 = 0;
    let mut v___y_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1708_: u8 = 0;
    let mut v___y_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1723_: u8 = 0;
    let mut v_inheritedTraceOptions_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: u8 = 0;
    let mut v___y_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1731_: u8 = 0;
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut v_unused_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1755_: u8 = 0;
    let mut v___y_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1772_: u8 = 0;
    let mut v_inheritedTraceOptions_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v_env_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v_reuseFailAlloc_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut v_unused_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1791_: u8 = 0;
    let mut v___y_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1795_: u8 = 0;
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v_unused_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___y_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1831_: u8 = 0;
    let mut v_inheritedTraceOptions_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v_env_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u8 = 0;
    let mut v___x_1844_: u8 = 0;
    let mut v_reuseFailAlloc_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: u8 = 0;
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1868_: u8 = 0;
    let mut v_unused_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v_reuseFailAlloc_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_unused_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_unused_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1609_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
                    v___x_1587_,
                    v___y_1595_,
                );
                v_a_1610_ = leanh::lean_ctor_get(v___x_1609_, 0);
                v_isSharedCheck_1878_ = (!leanh::lean_is_exclusive(v___x_1609_)) as u8;
                if v_isSharedCheck_1878_ == 0 {
                    v___x_1612_ = v___x_1609_;
                    v_isShared_1613_ = v_isSharedCheck_1878_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1610_);
                    leanh::lean_dec(v___x_1609_);
                    v___x_1612_ = leanh::lean_box(0);
                    v_isShared_1613_ = v_isSharedCheck_1878_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1600_ == 0 {
                    leanh::lean_dec_ref(v___y_1599_);
                    v___x_1601_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_1602_ = l_Lean_MessageData_ofName(v_tacticName_1590_);
                    v___x_1603_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1603_, 0, v___x_1601_);
                    leanh::lean_ctor_set(v___x_1603_, 1, v___x_1602_);
                    v___x_1604_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3,
                    );
                    v___x_1605_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1605_, 0, v___x_1603_);
                    leanh::lean_ctor_set(v___x_1605_, 1, v___x_1604_);
                    v___x_1606_ = l_Lean_Exception_toMessageData(v___y_1598_);
                    v___x_1607_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1607_, 0, v___x_1605_);
                    leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
                    v___x_1608_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1607_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
                    leanh::lean_dec_ref(v___y_1594_);
                    return v___x_1608_;
                } else {
                    leanh::lean_dec_ref(v___y_1598_);
                    leanh::lean_dec_ref(v___y_1594_);
                    leanh::lean_dec(v_tacticName_1590_);
                    return v___y_1599_;
                }
            }
            2 => {
                v___x_1640_ = lean_st_ref_take(v___y_1595_);
                v_env_1641_ = leanh::lean_ctor_get(v___x_1640_, 0);
                v_nextMacroScope_1642_ = leanh::lean_ctor_get(v___x_1640_, 1);
                v_ngen_1643_ = leanh::lean_ctor_get(v___x_1640_, 2);
                v_auxDeclNGen_1644_ = leanh::lean_ctor_get(v___x_1640_, 3);
                v_traceState_1645_ = leanh::lean_ctor_get(v___x_1640_, 4);
                v_messages_1646_ = leanh::lean_ctor_get(v___x_1640_, 6);
                v_infoState_1647_ = leanh::lean_ctor_get(v___x_1640_, 7);
                v_snapshotTasks_1648_ = leanh::lean_ctor_get(v___x_1640_, 8);
                v_isSharedCheck_1876_ = (!leanh::lean_is_exclusive(v___x_1640_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v_unused_1877_ = leanh::lean_ctor_get(v___x_1640_, 5);
                    leanh::lean_dec(v_unused_1877_);
                    v___x_1650_ = v___x_1640_;
                    v_isShared_1651_ = v_isSharedCheck_1876_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1648_);
                    leanh::lean_inc(v_infoState_1647_);
                    leanh::lean_inc(v_messages_1646_);
                    leanh::lean_inc(v_traceState_1645_);
                    leanh::lean_inc(v_auxDeclNGen_1644_);
                    leanh::lean_inc(v_ngen_1643_);
                    leanh::lean_inc(v_nextMacroScope_1642_);
                    leanh::lean_inc(v_env_1641_);
                    leanh::lean_dec(v___x_1640_);
                    v___x_1650_ = leanh::lean_box(0);
                    v_isShared_1651_ = v_isSharedCheck_1876_;
                    state = 7;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v___y_1615_) == 0 {
                    leanh::lean_dec_ref_known(v___y_1615_, 1);
                    v___x_1616_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
                        v_a_1610_,
                        v___y_1592_,
                        v___y_1593_,
                        v___y_1594_,
                        v___y_1595_,
                    );
                    if leanh::lean_obj_tag(v___x_1616_) == 0 {
                        leanh::lean_dec_ref(v___y_1594_);
                        leanh::lean_dec(v_tacticName_1590_);
                        return v___x_1616_;
                    } else {
                        v_a_1617_ = leanh::lean_ctor_get(v___x_1616_, 0);
                        leanh::lean_inc(v_a_1617_);
                        v___x_1618_ = l_Lean_Exception_isInterrupt(v_a_1617_);
                        if v___x_1618_ == 0 {
                            leanh::lean_inc(v_a_1617_);
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
                    leanh::lean_dec(v_a_1610_);
                    leanh::lean_dec_ref(v___y_1594_);
                    leanh::lean_dec(v_tacticName_1590_);
                    v_a_1620_ = leanh::lean_ctor_get(v___y_1615_, 0);
                    v_isSharedCheck_1627_ = (!leanh::lean_is_exclusive(v___y_1615_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v___x_1622_ = v___y_1615_;
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1620_);
                        leanh::lean_dec(v___y_1615_);
                        v___x_1622_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
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
                    leanh::lean_dec_ref(v___y_1630_);
                    v___x_1632_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    leanh::lean_inc(v_tacticName_1590_);
                    v___x_1633_ = l_Lean_MessageData_ofName(v_tacticName_1590_);
                    v___x_1634_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                    leanh::lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                    v___x_1635_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5,
                    );
                    v___x_1636_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1636_, 0, v___x_1634_);
                    leanh::lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                    v___x_1637_ = l_Lean_Exception_toMessageData(v___y_1629_);
                    v___x_1638_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1638_, 0, v___x_1636_);
                    leanh::lean_ctor_set(v___x_1638_, 1, v___x_1637_);
                    v___x_1639_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1638_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
                    v___y_1615_ = v___x_1639_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_1629_);
                    v___y_1615_ = v___y_1630_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_1652_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8,
                );
                leanh::lean_inc_n(v_a_1610_, 3);
                v___x_1653_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1653_, 0, v_a_1610_);
                leanh::lean_ctor_set(v___x_1653_, 1, v___x_1588_);
                leanh::lean_ctor_set(v___x_1653_, 2, v___x_1652_);
                v___x_1654_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1654_, 0, v_a_1610_);
                leanh::lean_ctor_set(v___x_1654_, 1, v___x_1589_);
                v___x_1655_ = l_Lean_markMeta(v_env_1641_, v_a_1610_);
                v___x_1656_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_1651_ == 0 {
                    leanh::lean_ctor_set(v___x_1650_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v___x_1650_, 0, v___x_1655_);
                    v___x_1658_ = v___x_1650_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_nextMacroScope_1642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_ngen_1643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_auxDeclNGen_1644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_traceState_1645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 6, v_messages_1646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 7, v_infoState_1647_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 8, v_snapshotTasks_1648_);
                    v___x_1658_ = v_reuseFailAlloc_1875_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1659_ = lean_st_ref_set(v___y_1595_, v___x_1658_);
                v___x_1660_ = lean_st_ref_take(v___y_1593_);
                v_mctx_1661_ = leanh::lean_ctor_get(v___x_1660_, 0);
                v_zetaDeltaFVarIds_1662_ = leanh::lean_ctor_get(v___x_1660_, 2);
                v_postponed_1663_ = leanh::lean_ctor_get(v___x_1660_, 3);
                v_diag_1664_ = leanh::lean_ctor_get(v___x_1660_, 4);
                v_isSharedCheck_1873_ = (!leanh::lean_is_exclusive(v___x_1660_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v_unused_1874_ = leanh::lean_ctor_get(v___x_1660_, 1);
                    leanh::lean_dec(v_unused_1874_);
                    v___x_1666_ = v___x_1660_;
                    v_isShared_1667_ = v_isSharedCheck_1873_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1664_);
                    leanh::lean_inc(v_postponed_1663_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1662_);
                    leanh::lean_inc(v_mctx_1661_);
                    leanh::lean_dec(v___x_1660_);
                    v___x_1666_ = leanh::lean_box(0);
                    v_isShared_1667_ = v_isSharedCheck_1873_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1668_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_1667_ == 0 {
                    leanh::lean_ctor_set(v___x_1666_, 1, v___x_1668_);
                    v___x_1670_ = v___x_1666_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_mctx_1661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1668_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1872_,
                        2,
                        v_zetaDeltaFVarIds_1662_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_postponed_1663_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_diag_1664_);
                    v___x_1670_ = v_reuseFailAlloc_1872_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1671_ = lean_st_ref_set(v___y_1593_, v___x_1670_);
                v___x_1672_ = lean_st_ref_get(v___y_1595_);
                v_options_1673_ = leanh::lean_ctor_get(v___y_1594_, 2);
                v_env_1674_ = leanh::lean_ctor_get(v___x_1672_, 0);
                leanh::lean_inc_ref(v_env_1674_);
                leanh::lean_dec(v___x_1672_);
                v___x_1675_ = leanh::lean_box(1);
                v___x_1676_ = 1;
                v___x_1677_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_1677_, 0, v___x_1653_);
                leanh::lean_ctor_set(v___x_1677_, 1, v_a_1591_);
                leanh::lean_ctor_set(v___x_1677_, 2, v___x_1675_);
                leanh::lean_ctor_set(v___x_1677_, 3, v___x_1654_);
                leanh::lean_ctor_set_uint8(
                    v___x_1677_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_1676_,
                );
                if v_isShared_1613_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1612_, 1);
                    leanh::lean_ctor_set(v___x_1612_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1612_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1677_);
                    v___x_1679_ = v_reuseFailAlloc_1871_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1680_ = 1;
                v___x_1681_ = 0;
                v___x_1751_ = l_Lean_Elab_async;
                leanh::lean_inc_ref(v_options_1673_);
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
                leanh::lean_dec_ref(v_env_1674_);
                if v___x_1870_ == 0 {
                    if v___x_1815_ == 0 {
                        leanh::lean_inc_ref(v___y_1594_);
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
                v___x_1701_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_1701_, 0, v_fileName_1686_);
                leanh::lean_ctor_set(v___x_1701_, 1, v_fileMap_1687_);
                leanh::lean_ctor_set(v___x_1701_, 2, v___y_1683_);
                leanh::lean_ctor_set(v___x_1701_, 3, v_currRecDepth_1688_);
                leanh::lean_ctor_set(v___x_1701_, 4, v___x_1700_);
                leanh::lean_ctor_set(v___x_1701_, 5, v_ref_1689_);
                leanh::lean_ctor_set(v___x_1701_, 6, v_currNamespace_1690_);
                leanh::lean_ctor_set(v___x_1701_, 7, v_openDecls_1691_);
                leanh::lean_ctor_set(v___x_1701_, 8, v_initHeartbeats_1692_);
                leanh::lean_ctor_set(v___x_1701_, 9, v_maxHeartbeats_1693_);
                leanh::lean_ctor_set(v___x_1701_, 10, v_quotContext_1694_);
                leanh::lean_ctor_set(v___x_1701_, 11, v_currMacroScope_1695_);
                leanh::lean_ctor_set(v___x_1701_, 12, v_cancelTk_x3f_1696_);
                leanh::lean_ctor_set(v___x_1701_, 13, v_inheritedTraceOptions_1698_);
                leanh::lean_ctor_set_uint8(
                    v___x_1701_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_1684_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1701_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1697_,
                );
                v___x_1702_ = l_Lean_addAndCompile(
                    v___x_1679_,
                    v___x_1680_,
                    v___x_1681_,
                    v___x_1701_,
                    v___y_1699_,
                );
                leanh::lean_dec_ref_known(v___x_1701_, 14);
                if leanh::lean_obj_tag(v___x_1702_) == 0 {
                    v___y_1615_ = v___x_1702_;
                    state = 3;
                    continue;
                } else {
                    v_a_1703_ = leanh::lean_ctor_get(v___x_1702_, 0);
                    leanh::lean_inc(v_a_1703_);
                    v___x_1704_ = l_Lean_Exception_isInterrupt(v_a_1703_);
                    if v___x_1704_ == 0 {
                        leanh::lean_inc(v_a_1703_);
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
                v_fileName_1712_ = leanh::lean_ctor_get(v___y_1710_, 0);
                leanh::lean_inc_ref(v_fileName_1712_);
                v_fileMap_1713_ = leanh::lean_ctor_get(v___y_1710_, 1);
                leanh::lean_inc_ref(v_fileMap_1713_);
                v_currRecDepth_1714_ = leanh::lean_ctor_get(v___y_1710_, 3);
                leanh::lean_inc(v_currRecDepth_1714_);
                v_ref_1715_ = leanh::lean_ctor_get(v___y_1710_, 5);
                leanh::lean_inc(v_ref_1715_);
                v_currNamespace_1716_ = leanh::lean_ctor_get(v___y_1710_, 6);
                leanh::lean_inc(v_currNamespace_1716_);
                v_openDecls_1717_ = leanh::lean_ctor_get(v___y_1710_, 7);
                leanh::lean_inc(v_openDecls_1717_);
                v_initHeartbeats_1718_ = leanh::lean_ctor_get(v___y_1710_, 8);
                leanh::lean_inc(v_initHeartbeats_1718_);
                v_maxHeartbeats_1719_ = leanh::lean_ctor_get(v___y_1710_, 9);
                leanh::lean_inc(v_maxHeartbeats_1719_);
                v_quotContext_1720_ = leanh::lean_ctor_get(v___y_1710_, 10);
                leanh::lean_inc(v_quotContext_1720_);
                v_currMacroScope_1721_ = leanh::lean_ctor_get(v___y_1710_, 11);
                leanh::lean_inc(v_currMacroScope_1721_);
                v_cancelTk_x3f_1722_ = leanh::lean_ctor_get(v___y_1710_, 12);
                leanh::lean_inc(v_cancelTk_x3f_1722_);
                v_suppressElabErrors_1723_ = leanh::lean_ctor_get_uint8(
                    v___y_1710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1724_ = leanh::lean_ctor_get(v___y_1710_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_1724_);
                leanh::lean_dec_ref(v___y_1710_);
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
                    v_env_1733_ = leanh::lean_ctor_get(v___x_1732_, 0);
                    v_nextMacroScope_1734_ = leanh::lean_ctor_get(v___x_1732_, 1);
                    v_ngen_1735_ = leanh::lean_ctor_get(v___x_1732_, 2);
                    v_auxDeclNGen_1736_ = leanh::lean_ctor_get(v___x_1732_, 3);
                    v_traceState_1737_ = leanh::lean_ctor_get(v___x_1732_, 4);
                    v_messages_1738_ = leanh::lean_ctor_get(v___x_1732_, 6);
                    v_infoState_1739_ = leanh::lean_ctor_get(v___x_1732_, 7);
                    v_snapshotTasks_1740_ = leanh::lean_ctor_get(v___x_1732_, 8);
                    v_isSharedCheck_1749_ = (!leanh::lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1749_ == 0 {
                        v_unused_1750_ = leanh::lean_ctor_get(v___x_1732_, 5);
                        leanh::lean_dec(v_unused_1750_);
                        v___x_1742_ = v___x_1732_;
                        v_isShared_1743_ = v_isSharedCheck_1749_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1740_);
                        leanh::lean_inc(v_infoState_1739_);
                        leanh::lean_inc(v_messages_1738_);
                        leanh::lean_inc(v_traceState_1737_);
                        leanh::lean_inc(v_auxDeclNGen_1736_);
                        leanh::lean_inc(v_ngen_1735_);
                        leanh::lean_inc(v_nextMacroScope_1734_);
                        leanh::lean_inc(v_env_1733_);
                        leanh::lean_dec(v___x_1732_);
                        v___x_1742_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_1742_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v___x_1742_, 0, v___x_1744_);
                    v___x_1746_ = v___x_1742_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1748_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_nextMacroScope_1734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_ngen_1735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_auxDeclNGen_1736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 4, v_traceState_1737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 6, v_messages_1738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 7, v_infoState_1739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 8, v_snapshotTasks_1740_);
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
                v_fileName_1761_ = leanh::lean_ctor_get(v___y_1758_, 0);
                v_fileMap_1762_ = leanh::lean_ctor_get(v___y_1758_, 1);
                v_currRecDepth_1763_ = leanh::lean_ctor_get(v___y_1758_, 3);
                v_ref_1764_ = leanh::lean_ctor_get(v___y_1758_, 5);
                v_currNamespace_1765_ = leanh::lean_ctor_get(v___y_1758_, 6);
                v_openDecls_1766_ = leanh::lean_ctor_get(v___y_1758_, 7);
                v_initHeartbeats_1767_ = leanh::lean_ctor_get(v___y_1758_, 8);
                v_maxHeartbeats_1768_ = leanh::lean_ctor_get(v___y_1758_, 9);
                v_quotContext_1769_ = leanh::lean_ctor_get(v___y_1758_, 10);
                v_currMacroScope_1770_ = leanh::lean_ctor_get(v___y_1758_, 11);
                v_cancelTk_x3f_1771_ = leanh::lean_ctor_get(v___y_1758_, 12);
                v_suppressElabErrors_1772_ = leanh::lean_ctor_get_uint8(
                    v___y_1758_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1773_ = leanh::lean_ctor_get(v___y_1758_, 13);
                v_isSharedCheck_1786_ = (!leanh::lean_is_exclusive(v___y_1758_)) as u8;
                if v_isSharedCheck_1786_ == 0 {
                    v_unused_1787_ = leanh::lean_ctor_get(v___y_1758_, 4);
                    leanh::lean_dec(v_unused_1787_);
                    v_unused_1788_ = leanh::lean_ctor_get(v___y_1758_, 2);
                    leanh::lean_dec(v_unused_1788_);
                    v___x_1775_ = v___y_1758_;
                    v_isShared_1776_ = v_isSharedCheck_1786_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_1773_);
                    leanh::lean_inc(v_cancelTk_x3f_1771_);
                    leanh::lean_inc(v_currMacroScope_1770_);
                    leanh::lean_inc(v_quotContext_1769_);
                    leanh::lean_inc(v_maxHeartbeats_1768_);
                    leanh::lean_inc(v_initHeartbeats_1767_);
                    leanh::lean_inc(v_openDecls_1766_);
                    leanh::lean_inc(v_currNamespace_1765_);
                    leanh::lean_inc(v_ref_1764_);
                    leanh::lean_inc(v_currRecDepth_1763_);
                    leanh::lean_inc(v_fileMap_1762_);
                    leanh::lean_inc(v_fileName_1761_);
                    leanh::lean_dec(v___y_1758_);
                    v___x_1775_ = leanh::lean_box(0);
                    v_isShared_1776_ = v_isSharedCheck_1786_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_env_1777_ = leanh::lean_ctor_get(v___x_1760_, 0);
                leanh::lean_inc_ref(v_env_1777_);
                leanh::lean_dec(v___x_1760_);
                v___x_1778_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
                    v___y_1756_,
                    v___y_1757_,
                );
                leanh::lean_inc_ref(v_inheritedTraceOptions_1773_);
                leanh::lean_inc(v_cancelTk_x3f_1771_);
                leanh::lean_inc(v_currMacroScope_1770_);
                leanh::lean_inc(v_quotContext_1769_);
                leanh::lean_inc(v_maxHeartbeats_1768_);
                leanh::lean_inc(v_initHeartbeats_1767_);
                leanh::lean_inc(v_openDecls_1766_);
                leanh::lean_inc(v_currNamespace_1765_);
                leanh::lean_inc(v_ref_1764_);
                leanh::lean_inc(v_currRecDepth_1763_);
                leanh::lean_inc_ref(v___y_1756_);
                leanh::lean_inc_ref(v_fileMap_1762_);
                leanh::lean_inc_ref(v_fileName_1761_);
                if v_isShared_1776_ == 0 {
                    leanh::lean_ctor_set(v___x_1775_, 4, v___x_1778_);
                    leanh::lean_ctor_set(v___x_1775_, 2, v___y_1756_);
                    v___x_1780_ = v___x_1775_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fileName_1761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_fileMap_1762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 2, v___y_1756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_currRecDepth_1763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 4, v___x_1778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_ref_1764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 6, v_currNamespace_1765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 7, v_openDecls_1766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 8, v_initHeartbeats_1767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 9, v_maxHeartbeats_1768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 10, v_quotContext_1769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 11, v_currMacroScope_1770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 12, v_cancelTk_x3f_1771_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1785_,
                        13,
                        v_inheritedTraceOptions_1773_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1785_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1772_,
                    );
                    v___x_1780_ = v_reuseFailAlloc_1785_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1780_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
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
                leanh::lean_dec_ref(v_env_1777_);
                if v___x_1784_ == 0 {
                    if v___x_1783_ == 0 {
                        leanh::lean_dec_ref(v___x_1780_);
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
                        leanh::lean_dec_ref(v_inheritedTraceOptions_1773_);
                        leanh::lean_dec(v_cancelTk_x3f_1771_);
                        leanh::lean_dec(v_currMacroScope_1770_);
                        leanh::lean_dec(v_quotContext_1769_);
                        leanh::lean_dec(v_maxHeartbeats_1768_);
                        leanh::lean_dec(v_initHeartbeats_1767_);
                        leanh::lean_dec(v_openDecls_1766_);
                        leanh::lean_dec(v_currNamespace_1765_);
                        leanh::lean_dec(v_ref_1764_);
                        leanh::lean_dec(v_currRecDepth_1763_);
                        leanh::lean_dec_ref(v_fileMap_1762_);
                        leanh::lean_dec_ref(v_fileName_1761_);
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
                    leanh::lean_dec_ref(v_inheritedTraceOptions_1773_);
                    leanh::lean_dec(v_cancelTk_x3f_1771_);
                    leanh::lean_dec(v_currMacroScope_1770_);
                    leanh::lean_dec(v_quotContext_1769_);
                    leanh::lean_dec(v_maxHeartbeats_1768_);
                    leanh::lean_dec(v_initHeartbeats_1767_);
                    leanh::lean_dec(v_openDecls_1766_);
                    leanh::lean_dec(v_currNamespace_1765_);
                    leanh::lean_dec(v_ref_1764_);
                    leanh::lean_dec(v_currRecDepth_1763_);
                    leanh::lean_dec_ref(v_fileMap_1762_);
                    leanh::lean_dec_ref(v_fileName_1761_);
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
                    v_env_1797_ = leanh::lean_ctor_get(v___x_1796_, 0);
                    v_nextMacroScope_1798_ = leanh::lean_ctor_get(v___x_1796_, 1);
                    v_ngen_1799_ = leanh::lean_ctor_get(v___x_1796_, 2);
                    v_auxDeclNGen_1800_ = leanh::lean_ctor_get(v___x_1796_, 3);
                    v_traceState_1801_ = leanh::lean_ctor_get(v___x_1796_, 4);
                    v_messages_1802_ = leanh::lean_ctor_get(v___x_1796_, 6);
                    v_infoState_1803_ = leanh::lean_ctor_get(v___x_1796_, 7);
                    v_snapshotTasks_1804_ = leanh::lean_ctor_get(v___x_1796_, 8);
                    v_isSharedCheck_1813_ = (!leanh::lean_is_exclusive(v___x_1796_)) as u8;
                    if v_isSharedCheck_1813_ == 0 {
                        v_unused_1814_ = leanh::lean_ctor_get(v___x_1796_, 5);
                        leanh::lean_dec(v_unused_1814_);
                        v___x_1806_ = v___x_1796_;
                        v_isShared_1807_ = v_isSharedCheck_1813_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1804_);
                        leanh::lean_inc(v_infoState_1803_);
                        leanh::lean_inc(v_messages_1802_);
                        leanh::lean_inc(v_traceState_1801_);
                        leanh::lean_inc(v_auxDeclNGen_1800_);
                        leanh::lean_inc(v_ngen_1799_);
                        leanh::lean_inc(v_nextMacroScope_1798_);
                        leanh::lean_inc(v_env_1797_);
                        leanh::lean_dec(v___x_1796_);
                        v___x_1806_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_1806_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v___x_1806_, 0, v___x_1808_);
                    v___x_1810_ = v___x_1806_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_nextMacroScope_1798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_ngen_1799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_auxDeclNGen_1800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_traceState_1801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 6, v_messages_1802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 7, v_infoState_1803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 8, v_snapshotTasks_1804_);
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
                v_fileName_1820_ = leanh::lean_ctor_get(v___y_1817_, 0);
                v_fileMap_1821_ = leanh::lean_ctor_get(v___y_1817_, 1);
                v_currRecDepth_1822_ = leanh::lean_ctor_get(v___y_1817_, 3);
                v_ref_1823_ = leanh::lean_ctor_get(v___y_1817_, 5);
                v_currNamespace_1824_ = leanh::lean_ctor_get(v___y_1817_, 6);
                v_openDecls_1825_ = leanh::lean_ctor_get(v___y_1817_, 7);
                v_initHeartbeats_1826_ = leanh::lean_ctor_get(v___y_1817_, 8);
                v_maxHeartbeats_1827_ = leanh::lean_ctor_get(v___y_1817_, 9);
                v_quotContext_1828_ = leanh::lean_ctor_get(v___y_1817_, 10);
                v_currMacroScope_1829_ = leanh::lean_ctor_get(v___y_1817_, 11);
                v_cancelTk_x3f_1830_ = leanh::lean_ctor_get(v___y_1817_, 12);
                v_suppressElabErrors_1831_ = leanh::lean_ctor_get_uint8(
                    v___y_1817_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1832_ = leanh::lean_ctor_get(v___y_1817_, 13);
                v_isSharedCheck_1846_ = (!leanh::lean_is_exclusive(v___y_1817_)) as u8;
                if v_isSharedCheck_1846_ == 0 {
                    v_unused_1847_ = leanh::lean_ctor_get(v___y_1817_, 4);
                    leanh::lean_dec(v_unused_1847_);
                    v_unused_1848_ = leanh::lean_ctor_get(v___y_1817_, 2);
                    leanh::lean_dec(v_unused_1848_);
                    v___x_1834_ = v___y_1817_;
                    v_isShared_1835_ = v_isSharedCheck_1846_;
                    state = 24;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_1832_);
                    leanh::lean_inc(v_cancelTk_x3f_1830_);
                    leanh::lean_inc(v_currMacroScope_1829_);
                    leanh::lean_inc(v_quotContext_1828_);
                    leanh::lean_inc(v_maxHeartbeats_1827_);
                    leanh::lean_inc(v_initHeartbeats_1826_);
                    leanh::lean_inc(v_openDecls_1825_);
                    leanh::lean_inc(v_currNamespace_1824_);
                    leanh::lean_inc(v_ref_1823_);
                    leanh::lean_inc(v_currRecDepth_1822_);
                    leanh::lean_inc(v_fileMap_1821_);
                    leanh::lean_inc(v_fileName_1820_);
                    leanh::lean_dec(v___y_1817_);
                    v___x_1834_ = leanh::lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1846_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_env_1836_ = leanh::lean_ctor_get(v___x_1819_, 0);
                leanh::lean_inc_ref(v_env_1836_);
                leanh::lean_dec(v___x_1819_);
                v___x_1837_ = l_Lean_maxRecDepth;
                v___x_1838_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
                    v___x_1752_,
                    v___x_1837_,
                );
                leanh::lean_inc_ref(v___x_1752_);
                if v_isShared_1835_ == 0 {
                    leanh::lean_ctor_set(v___x_1834_, 4, v___x_1838_);
                    leanh::lean_ctor_set(v___x_1834_, 2, v___x_1752_);
                    v___x_1840_ = v___x_1834_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fileName_1820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_fileMap_1821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 2, v___x_1752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_currRecDepth_1822_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 4, v___x_1838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_ref_1823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_currNamespace_1824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_openDecls_1825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 8, v_initHeartbeats_1826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_maxHeartbeats_1827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 10, v_quotContext_1828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 11, v_currMacroScope_1829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 12, v_cancelTk_x3f_1830_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1845_,
                        13,
                        v_inheritedTraceOptions_1832_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1845_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1831_,
                    );
                    v___x_1840_ = v_reuseFailAlloc_1845_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1840_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
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
                leanh::lean_dec_ref(v_env_1836_);
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
                    v_env_1852_ = leanh::lean_ctor_get(v___x_1851_, 0);
                    v_nextMacroScope_1853_ = leanh::lean_ctor_get(v___x_1851_, 1);
                    v_ngen_1854_ = leanh::lean_ctor_get(v___x_1851_, 2);
                    v_auxDeclNGen_1855_ = leanh::lean_ctor_get(v___x_1851_, 3);
                    v_traceState_1856_ = leanh::lean_ctor_get(v___x_1851_, 4);
                    v_messages_1857_ = leanh::lean_ctor_get(v___x_1851_, 6);
                    v_infoState_1858_ = leanh::lean_ctor_get(v___x_1851_, 7);
                    v_snapshotTasks_1859_ = leanh::lean_ctor_get(v___x_1851_, 8);
                    v_isSharedCheck_1868_ = (!leanh::lean_is_exclusive(v___x_1851_)) as u8;
                    if v_isSharedCheck_1868_ == 0 {
                        v_unused_1869_ = leanh::lean_ctor_get(v___x_1851_, 5);
                        leanh::lean_dec(v_unused_1869_);
                        v___x_1861_ = v___x_1851_;
                        v_isShared_1862_ = v_isSharedCheck_1868_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1859_);
                        leanh::lean_inc(v_infoState_1858_);
                        leanh::lean_inc(v_messages_1857_);
                        leanh::lean_inc(v_traceState_1856_);
                        leanh::lean_inc(v_auxDeclNGen_1855_);
                        leanh::lean_inc(v_ngen_1854_);
                        leanh::lean_inc(v_nextMacroScope_1853_);
                        leanh::lean_inc(v_env_1852_);
                        leanh::lean_dec(v___x_1851_);
                        v___x_1861_ = leanh::lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1868_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v___y_1594_);
                    v___y_1817_ = v___y_1594_;
                    v___y_1818_ = v___y_1595_;
                    state = 23;
                    continue;
                }
            }
            27 => {
                v___x_1863_ = l_Lean_Kernel_enableDiag(v_env_1852_, v___x_1815_);
                if v_isShared_1862_ == 0 {
                    leanh::lean_ctor_set(v___x_1861_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v___x_1861_, 0, v___x_1863_);
                    v___x_1865_ = v___x_1861_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_nextMacroScope_1853_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_ngen_1854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_auxDeclNGen_1855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_traceState_1856_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 5, v___x_1656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_messages_1857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 7, v_infoState_1858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_snapshotTasks_1859_);
                    v___x_1865_ = v_reuseFailAlloc_1867_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_1866_ = lean_st_ref_set(v___y_1595_, v___x_1865_);
                leanh::lean_inc_ref(v___y_1594_);
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
    mut v___x_1879_: *mut leanh::LeanObject,
    mut v___x_1880_: *mut leanh::LeanObject,
    mut v___x_1881_: *mut leanh::LeanObject,
    mut v_tacticName_1882_: *mut leanh::LeanObject,
    mut v_a_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1887_);
    leanh::lean_dec(v___y_1885_);
    leanh::lean_dec_ref(v___y_1884_);
    return v_res_1889_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(
    mut v_stx_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v_fileMap_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1893_ = 0;
                v___x_1894_ = l_Lean_Syntax_getRange_x3f(v_stx_1890_, v___x_1893_);
                if leanh::lean_obj_tag(v___x_1894_) == 1 {
                    v_val_1895_ = leanh::lean_ctor_get(v___x_1894_, 0);
                    v_isSharedCheck_1907_ = (!leanh::lean_is_exclusive(v___x_1894_)) as u8;
                    if v_isSharedCheck_1907_ == 0 {
                        v___x_1897_ = v___x_1894_;
                        v_isShared_1898_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1895_);
                        leanh::lean_dec(v___x_1894_);
                        v___x_1897_ = leanh::lean_box(0);
                        v_isShared_1898_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1894_);
                    v___x_1908_ = leanh::lean_box(0);
                    v___x_1909_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1909_, 0, v___x_1908_);
                    return v___x_1909_;
                }
            }
            1 => {
                v_fileMap_1899_ = leanh::lean_ctor_get(v___y_1891_, 1);
                v_start_1900_ = leanh::lean_ctor_get(v_val_1895_, 0);
                leanh::lean_inc(v_start_1900_);
                v_stop_1901_ = leanh::lean_ctor_get(v_val_1895_, 1);
                leanh::lean_inc(v_stop_1901_);
                leanh::lean_dec(v_val_1895_);
                leanh::lean_inc_ref(v_fileMap_1899_);
                v___x_1902_ = l_Lean_DeclarationRange_ofStringPositions(
                    v_fileMap_1899_,
                    v_start_1900_,
                    v_stop_1901_,
                );
                leanh::lean_dec(v_stop_1901_);
                leanh::lean_dec(v_start_1900_);
                if v_isShared_1898_ == 0 {
                    leanh::lean_ctor_set(v___x_1897_, 0, v___x_1902_);
                    v___x_1904_ = v___x_1897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1902_);
                    v___x_1904_ = v_reuseFailAlloc_1906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1905_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                return v___x_1905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(
    mut v_stx_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_1910_, v___y_1911_);
    leanh::lean_dec_ref(v___y_1911_);
    leanh::lean_dec(v_stx_1910_);
    return v_res_1913_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(
    mut v_declName_1914_: *mut leanh::LeanObject,
    mut v_declRanges_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
    mut v___y_1917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1945_: u8 = 0;
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut v_unused_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut v_unused_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1919_ = l_Lean_Name_isAnonymous(v_declName_1914_);
                if v___x_1919_ == 0 {
                    v___x_1920_ = lean_st_ref_take(v___y_1917_);
                    v_env_1921_ = leanh::lean_ctor_get(v___x_1920_, 0);
                    v_nextMacroScope_1922_ = leanh::lean_ctor_get(v___x_1920_, 1);
                    v_ngen_1923_ = leanh::lean_ctor_get(v___x_1920_, 2);
                    v_auxDeclNGen_1924_ = leanh::lean_ctor_get(v___x_1920_, 3);
                    v_traceState_1925_ = leanh::lean_ctor_get(v___x_1920_, 4);
                    v_messages_1926_ = leanh::lean_ctor_get(v___x_1920_, 6);
                    v_infoState_1927_ = leanh::lean_ctor_get(v___x_1920_, 7);
                    v_snapshotTasks_1928_ = leanh::lean_ctor_get(v___x_1920_, 8);
                    v_isSharedCheck_1956_ = (!leanh::lean_is_exclusive(v___x_1920_)) as u8;
                    if v_isSharedCheck_1956_ == 0 {
                        v_unused_1957_ = leanh::lean_ctor_get(v___x_1920_, 5);
                        leanh::lean_dec(v_unused_1957_);
                        v___x_1930_ = v___x_1920_;
                        v_isShared_1931_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1928_);
                        leanh::lean_inc(v_infoState_1927_);
                        leanh::lean_inc(v_messages_1926_);
                        leanh::lean_inc(v_traceState_1925_);
                        leanh::lean_inc(v_auxDeclNGen_1924_);
                        leanh::lean_inc(v_ngen_1923_);
                        leanh::lean_inc(v_nextMacroScope_1922_);
                        leanh::lean_inc(v_env_1921_);
                        leanh::lean_dec(v___x_1920_);
                        v___x_1930_ = leanh::lean_box(0);
                        v_isShared_1931_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_declRanges_1915_);
                    leanh::lean_dec(v_declName_1914_);
                    v___x_1958_ = leanh::lean_box(0);
                    v___x_1959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1959_, 0, v___x_1958_);
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
                v___x_1934_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_1931_ == 0 {
                    leanh::lean_ctor_set(v___x_1930_, 5, v___x_1934_);
                    leanh::lean_ctor_set(v___x_1930_, 0, v___x_1933_);
                    v___x_1936_ = v___x_1930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1955_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_nextMacroScope_1922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_ngen_1923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_auxDeclNGen_1924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_traceState_1925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 5, v___x_1934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_messages_1926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 7, v_infoState_1927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 8, v_snapshotTasks_1928_);
                    v___x_1936_ = v_reuseFailAlloc_1955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1937_ = lean_st_ref_set(v___y_1917_, v___x_1936_);
                v___x_1938_ = lean_st_ref_take(v___y_1916_);
                v_mctx_1939_ = leanh::lean_ctor_get(v___x_1938_, 0);
                v_zetaDeltaFVarIds_1940_ = leanh::lean_ctor_get(v___x_1938_, 2);
                v_postponed_1941_ = leanh::lean_ctor_get(v___x_1938_, 3);
                v_diag_1942_ = leanh::lean_ctor_get(v___x_1938_, 4);
                v_isSharedCheck_1953_ = (!leanh::lean_is_exclusive(v___x_1938_)) as u8;
                if v_isSharedCheck_1953_ == 0 {
                    v_unused_1954_ = leanh::lean_ctor_get(v___x_1938_, 1);
                    leanh::lean_dec(v_unused_1954_);
                    v___x_1944_ = v___x_1938_;
                    v_isShared_1945_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1942_);
                    leanh::lean_inc(v_postponed_1941_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1940_);
                    leanh::lean_inc(v_mctx_1939_);
                    leanh::lean_dec(v___x_1938_);
                    v___x_1944_ = leanh::lean_box(0);
                    v_isShared_1945_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1946_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_1945_ == 0 {
                    leanh::lean_ctor_set(v___x_1944_, 1, v___x_1946_);
                    v___x_1948_ = v___x_1944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_mctx_1939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1946_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1952_,
                        2,
                        v_zetaDeltaFVarIds_1940_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_postponed_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_diag_1942_);
                    v___x_1948_ = v_reuseFailAlloc_1952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1949_ = lean_st_ref_set(v___y_1916_, v___x_1948_);
                v___x_1950_ = leanh::lean_box(0);
                v___x_1951_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1951_, 0, v___x_1950_);
                return v___x_1951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(
    mut v_declName_1960_: *mut leanh::LeanObject,
    mut v_declRanges_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
    mut v___y_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1960_, v_declRanges_1961_, v___y_1962_, v___y_1963_);
    leanh::lean_dec(v___y_1963_);
    leanh::lean_dec(v___y_1962_);
    return v_res_1965_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(
    mut v_declName_1966_: *mut leanh::LeanObject,
    mut v_rangeStx_1967_: *mut leanh::LeanObject,
    mut v_selectionRangeStx_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
    mut v___y_1970_: *mut leanh::LeanObject,
    mut v___y_1971_: *mut leanh::LeanObject,
    mut v___y_1972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_val_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1974_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_rangeStx_1967_, v___y_1971_);
                v_a_1975_ = leanh::lean_ctor_get(v___x_1974_, 0);
                v_isSharedCheck_1991_ = (!leanh::lean_is_exclusive(v___x_1974_)) as u8;
                if v_isSharedCheck_1991_ == 0 {
                    v___x_1977_ = v___x_1974_;
                    v_isShared_1978_ = v_isSharedCheck_1991_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1975_);
                    leanh::lean_dec(v___x_1974_);
                    v___x_1977_ = leanh::lean_box(0);
                    v_isShared_1978_ = v_isSharedCheck_1991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1975_) == 1 {
                    leanh::lean_del_object(v___x_1977_);
                    v_val_1979_ = leanh::lean_ctor_get(v_a_1975_, 0);
                    leanh::lean_inc(v_val_1979_);
                    leanh::lean_dec_ref_known(v_a_1975_, 1);
                    v___x_1980_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_selectionRangeStx_1968_, v___y_1971_);
                    v_a_1981_ = leanh::lean_ctor_get(v___x_1980_, 0);
                    leanh::lean_inc(v_a_1981_);
                    leanh::lean_dec_ref(v___x_1980_);
                    if leanh::lean_obj_tag(v_a_1981_) == 0 {
                        leanh::lean_inc(v_val_1979_);
                        v_a_1983_ = v_val_1979_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1986_ = leanh::lean_ctor_get(v_a_1981_, 0);
                        leanh::lean_inc(v_val_1986_);
                        leanh::lean_dec_ref_known(v_a_1981_, 1);
                        v_a_1983_ = v_val_1986_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1975_);
                    leanh::lean_dec(v_declName_1966_);
                    v___x_1987_ = leanh::lean_box(0);
                    if v_isShared_1978_ == 0 {
                        leanh::lean_ctor_set(v___x_1977_, 0, v___x_1987_);
                        v___x_1989_ = v___x_1977_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
                        v___x_1989_ = v_reuseFailAlloc_1990_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1984_, 0, v_val_1979_);
                leanh::lean_ctor_set(v___x_1984_, 1, v_a_1983_);
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
    mut v_declName_1992_: *mut leanh::LeanObject,
    mut v_rangeStx_1993_: *mut leanh::LeanObject,
    mut v_selectionRangeStx_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1998_);
    leanh::lean_dec_ref(v___y_1997_);
    leanh::lean_dec(v___y_1996_);
    leanh::lean_dec_ref(v___y_1995_);
    leanh::lean_dec(v_selectionRangeStx_1994_);
    leanh::lean_dec(v_rangeStx_1993_);
    return v_res_2000_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(
    mut v_a_2001_: *mut leanh::LeanObject,
    mut v_a_2002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2001_) == 0 {
                    v___x_2003_ = l_List_reverse___redArg(v_a_2002_);
                    return v___x_2003_;
                } else {
                    v_head_2004_ = leanh::lean_ctor_get(v_a_2001_, 0);
                    v_tail_2005_ = leanh::lean_ctor_get(v_a_2001_, 1);
                    v_isSharedCheck_2014_ = (!leanh::lean_is_exclusive(v_a_2001_)) as u8;
                    if v_isSharedCheck_2014_ == 0 {
                        v___x_2007_ = v_a_2001_;
                        v_isShared_2008_ = v_isSharedCheck_2014_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2005_);
                        leanh::lean_inc(v_head_2004_);
                        leanh::lean_dec(v_a_2001_);
                        v___x_2007_ = leanh::lean_box(0);
                        v_isShared_2008_ = v_isSharedCheck_2014_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2009_ = l_Lean_mkLevelParam(v_head_2004_);
                if v_isShared_2008_ == 0 {
                    leanh::lean_ctor_set(v___x_2007_, 1, v_a_2002_);
                    leanh::lean_ctor_set(v___x_2007_, 0, v___x_2009_);
                    v___x_2011_ = v___x_2007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_a_2002_);
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
    mut v_env_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_unused_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_unused_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2019_ = lean_st_ref_take(v___y_2017_);
                v_nextMacroScope_2020_ = leanh::lean_ctor_get(v___x_2019_, 1);
                v_ngen_2021_ = leanh::lean_ctor_get(v___x_2019_, 2);
                v_auxDeclNGen_2022_ = leanh::lean_ctor_get(v___x_2019_, 3);
                v_traceState_2023_ = leanh::lean_ctor_get(v___x_2019_, 4);
                v_messages_2024_ = leanh::lean_ctor_get(v___x_2019_, 6);
                v_infoState_2025_ = leanh::lean_ctor_get(v___x_2019_, 7);
                v_snapshotTasks_2026_ = leanh::lean_ctor_get(v___x_2019_, 8);
                v_isSharedCheck_2052_ = (!leanh::lean_is_exclusive(v___x_2019_)) as u8;
                if v_isSharedCheck_2052_ == 0 {
                    v_unused_2053_ = leanh::lean_ctor_get(v___x_2019_, 5);
                    leanh::lean_dec(v_unused_2053_);
                    v_unused_2054_ = leanh::lean_ctor_get(v___x_2019_, 0);
                    leanh::lean_dec(v_unused_2054_);
                    v___x_2028_ = v___x_2019_;
                    v_isShared_2029_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2026_);
                    leanh::lean_inc(v_infoState_2025_);
                    leanh::lean_inc(v_messages_2024_);
                    leanh::lean_inc(v_traceState_2023_);
                    leanh::lean_inc(v_auxDeclNGen_2022_);
                    leanh::lean_inc(v_ngen_2021_);
                    leanh::lean_inc(v_nextMacroScope_2020_);
                    leanh::lean_dec(v___x_2019_);
                    v___x_2028_ = leanh::lean_box(0);
                    v_isShared_2029_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2030_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_2029_ == 0 {
                    leanh::lean_ctor_set(v___x_2028_, 5, v___x_2030_);
                    leanh::lean_ctor_set(v___x_2028_, 0, v_env_2015_);
                    v___x_2032_ = v___x_2028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_env_2015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_nextMacroScope_2020_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_ngen_2021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_auxDeclNGen_2022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_traceState_2023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 5, v___x_2030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 6, v_messages_2024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 7, v_infoState_2025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 8, v_snapshotTasks_2026_);
                    v___x_2032_ = v_reuseFailAlloc_2051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2033_ = lean_st_ref_set(v___y_2017_, v___x_2032_);
                v___x_2034_ = lean_st_ref_take(v___y_2016_);
                v_mctx_2035_ = leanh::lean_ctor_get(v___x_2034_, 0);
                v_zetaDeltaFVarIds_2036_ = leanh::lean_ctor_get(v___x_2034_, 2);
                v_postponed_2037_ = leanh::lean_ctor_get(v___x_2034_, 3);
                v_diag_2038_ = leanh::lean_ctor_get(v___x_2034_, 4);
                v_isSharedCheck_2049_ = (!leanh::lean_is_exclusive(v___x_2034_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v_unused_2050_ = leanh::lean_ctor_get(v___x_2034_, 1);
                    leanh::lean_dec(v_unused_2050_);
                    v___x_2040_ = v___x_2034_;
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2038_);
                    leanh::lean_inc(v_postponed_2037_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2036_);
                    leanh::lean_inc(v_mctx_2035_);
                    leanh::lean_dec(v___x_2034_);
                    v___x_2040_ = leanh::lean_box(0);
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2042_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_2041_ == 0 {
                    leanh::lean_ctor_set(v___x_2040_, 1, v___x_2042_);
                    v___x_2044_ = v___x_2040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_mctx_2035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2042_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2048_,
                        2,
                        v_zetaDeltaFVarIds_2036_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_postponed_2037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_diag_2038_);
                    v___x_2044_ = v_reuseFailAlloc_2048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2045_ = lean_st_ref_set(v___y_2016_, v___x_2044_);
                v___x_2046_ = leanh::lean_box(0);
                v___x_2047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                return v___x_2047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(
    mut v_env_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2055_, v___y_2056_, v___y_2057_);
    leanh::lean_dec(v___y_2057_);
    leanh::lean_dec(v___y_2056_);
    return v_res_2059_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
    mut v_env_2060_: *mut leanh::LeanObject,
    mut v_x_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
    mut v___y_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2074_: u8 = 0;
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v_unused_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_unused_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2067_ = lean_st_ref_get(v___y_2065_);
                v_env_2068_ = leanh::lean_ctor_get(v___x_2067_, 0);
                leanh::lean_inc_ref(v_env_2068_);
                leanh::lean_dec(v___x_2067_);
                v___x_2080_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2060_, v___y_2063_, v___y_2065_);
                leanh::lean_dec_ref(v___x_2080_);
                leanh::lean_inc(v___y_2065_);
                leanh::lean_inc_ref(v___y_2064_);
                leanh::lean_inc(v___y_2063_);
                leanh::lean_inc_ref(v___y_2062_);
                v___x_2081_ = leanh::lean_apply_5(
                    v_x_2061_,
                    v___y_2062_,
                    v___y_2063_,
                    v___y_2064_,
                    v___y_2065_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2081_) == 0 {
                    v_a_2082_ = leanh::lean_ctor_get(v___x_2081_, 0);
                    leanh::lean_inc(v_a_2082_);
                    leanh::lean_dec_ref_known(v___x_2081_, 1);
                    v___x_2083_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2068_, v___y_2063_, v___y_2065_);
                    v_isSharedCheck_2090_ = (!leanh::lean_is_exclusive(v___x_2083_)) as u8;
                    if v_isSharedCheck_2090_ == 0 {
                        v_unused_2091_ = leanh::lean_ctor_get(v___x_2083_, 0);
                        leanh::lean_dec(v_unused_2091_);
                        v___x_2085_ = v___x_2083_;
                        v_isShared_2086_ = v_isSharedCheck_2090_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2083_);
                        v___x_2085_ = leanh::lean_box(0);
                        v_isShared_2086_ = v_isSharedCheck_2090_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2092_ = leanh::lean_ctor_get(v___x_2081_, 0);
                    leanh::lean_inc(v_a_2092_);
                    leanh::lean_dec_ref_known(v___x_2081_, 1);
                    v_a_2070_ = v_a_2092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2071_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2068_, v___y_2063_, v___y_2065_);
                v_isSharedCheck_2078_ = (!leanh::lean_is_exclusive(v___x_2071_)) as u8;
                if v_isSharedCheck_2078_ == 0 {
                    v_unused_2079_ = leanh::lean_ctor_get(v___x_2071_, 0);
                    leanh::lean_dec(v_unused_2079_);
                    v___x_2073_ = v___x_2071_;
                    v_isShared_2074_ = v_isSharedCheck_2078_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2071_);
                    v___x_2073_ = leanh::lean_box(0);
                    v_isShared_2074_ = v_isSharedCheck_2078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2074_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2073_, 1);
                    leanh::lean_ctor_set(v___x_2073_, 0, v_a_2070_);
                    v___x_2076_ = v___x_2073_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2077_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2070_);
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
                    leanh::lean_ctor_set(v___x_2085_, 0, v_a_2082_);
                    v___x_2088_ = v___x_2085_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2082_);
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
    mut v_env_2093_: *mut leanh::LeanObject,
    mut v_x_2094_: *mut leanh::LeanObject,
    mut v___y_2095_: *mut leanh::LeanObject,
    mut v___y_2096_: *mut leanh::LeanObject,
    mut v___y_2097_: *mut leanh::LeanObject,
    mut v___y_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
        v_env_2093_,
        v_x_2094_,
        v___y_2095_,
        v___y_2096_,
        v___y_2097_,
        v___y_2098_,
    );
    leanh::lean_dec(v___y_2098_);
    leanh::lean_dec_ref(v___y_2097_);
    leanh::lean_dec(v___y_2096_);
    leanh::lean_dec_ref(v___y_2095_);
    return v_res_2100_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = leanh::lean_box(0);
    v___x_2102_ = leanh::lean_unsigned_to_nat(16);
    v___x_2103_ = lean_mk_array(v___x_2102_, v___x_2101_);
    return v___x_2103_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__0_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__0,
    );
    v___x_2105_ = leanh::lean_unsigned_to_nat(0);
    v___x_2106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2106_, 0, v___x_2105_);
    leanh::lean_ctor_set(v___x_2106_, 1, v___x_2104_);
    return v___x_2106_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_Meta_nativeEqTrue___closed__2;
    v___x_2110_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__1_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__1,
    );
    v___x_2111_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2111_, 0, v___x_2110_);
    leanh::lean_ctor_set(v___x_2111_, 1, v___x_2110_);
    leanh::lean_ctor_set(v___x_2111_, 2, v___x_2109_);
    return v___x_2111_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = leanh::lean_unsigned_to_nat(1);
    v___x_2125_ = l_Lean_Level_ofNat(v___x_2124_);
    return v___x_2125_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = leanh::lean_box(0);
    v___x_2127_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__12_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__12,
    );
    v___x_2128_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2128_, 0, v___x_2127_);
    leanh::lean_ctor_set(v___x_2128_, 1, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2129_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__13_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__13,
    );
    v___x_2130_ = l_Lean_Meta_nativeEqTrue___closed__11;
    v___x_2131_ = l_Lean_mkConst(v___x_2130_, v___x_2129_);
    return v___x_2131_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = leanh::lean_box(0);
    v___x_2133_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__7;
    v___x_2134_ = l_Lean_mkConst(v___x_2133_, v___x_2132_);
    return v___x_2134_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = leanh::lean_box(0);
    v___x_2140_ = l_Lean_Meta_nativeEqTrue___closed__17;
    v___x_2141_ = l_Lean_mkConst(v___x_2140_, v___x_2139_);
    return v___x_2141_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_Meta_nativeEqTrue___closed__19;
    v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = l_Lean_Meta_nativeEqTrue___closed__21;
    v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn l_Lean_Meta_nativeEqTrue(
    mut v_tacticName_2148_: *mut leanh::LeanObject,
    mut v_e_2149_: *mut leanh::LeanObject,
    mut v_axiomDeclRange_x3f_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
    mut v_a_2152_: *mut leanh::LeanObject,
    mut v_a_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v_env_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v___x_2192_: u8 = 0;
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_a_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_reuseFailAlloc_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut v_unused_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2164_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
                        v_e_2149_, v_a_2152_,
                    );
                v_a_2165_ = leanh::lean_ctor_get(v___x_2164_, 0);
                leanh::lean_inc(v_a_2165_);
                leanh::lean_dec_ref(v___x_2164_);
                v___x_2271_ = l_Lean_Expr_hasFVar(v_a_2165_);
                if v___x_2271_ == 0 {
                    v___y_2250_ = v_a_2151_;
                    v___y_2251_ = v_a_2152_;
                    v___y_2252_ = v_a_2153_;
                    v___y_2253_ = v_a_2154_;
                    state = 15;
                    continue;
                } else {
                    v___x_2272_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_2273_ = l_Lean_MessageData_ofName(v_tacticName_2148_);
                    v___x_2274_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2274_, 0, v___x_2272_);
                    leanh::lean_ctor_set(v___x_2274_, 1, v___x_2273_);
                    v___x_2275_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__22),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__22_once),
                        _init_l_Lean_Meta_nativeEqTrue___closed__22,
                    );
                    v___x_2276_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2276_, 0, v___x_2274_);
                    leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                    v___x_2277_ = l_Lean_indentExpr(v_a_2165_);
                    v___x_2278_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2278_, 0, v___x_2276_);
                    leanh::lean_ctor_set(v___x_2278_, 1, v___x_2277_);
                    v___x_2279_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2278_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
                    v_a_2280_ = leanh::lean_ctor_get(v___x_2279_, 0);
                    v_isSharedCheck_2287_ = (!leanh::lean_is_exclusive(v___x_2279_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2282_ = v___x_2279_;
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2280_);
                        leanh::lean_dec(v___x_2279_);
                        v___x_2282_ = leanh::lean_box(0);
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2159_ = leanh::lean_box(0);
                v___x_2160_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(
                    v___y_2158_,
                    v___x_2159_,
                );
                v___x_2161_ = l_Lean_mkConst(v___y_2157_, v___x_2160_);
                v___x_2162_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2162_, 0, v___x_2161_);
                v___x_2163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2163_, 0, v___x_2162_);
                return v___x_2163_;
            }
            2 => {
                v___x_2171_ = lean_st_ref_get(v___y_2170_);
                v___x_2172_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__3_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__3,
                );
                leanh::lean_inc(v_a_2165_);
                v___x_2173_ = l_Lean_collectLevelParams(v___x_2172_, v_a_2165_);
                v_params_2174_ = leanh::lean_ctor_get(v___x_2173_, 2);
                v_isSharedCheck_2246_ = (!leanh::lean_is_exclusive(v___x_2173_)) as u8;
                if v_isSharedCheck_2246_ == 0 {
                    v_unused_2247_ = leanh::lean_ctor_get(v___x_2173_, 1);
                    leanh::lean_dec(v_unused_2247_);
                    v_unused_2248_ = leanh::lean_ctor_get(v___x_2173_, 0);
                    leanh::lean_dec(v_unused_2248_);
                    v___x_2176_ = v___x_2173_;
                    v_isShared_2177_ = v_isSharedCheck_2246_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_params_2174_);
                    leanh::lean_dec(v___x_2173_);
                    v___x_2176_ = leanh::lean_box(0);
                    v_isShared_2177_ = v_isSharedCheck_2246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_env_2178_ = leanh::lean_ctor_get(v___x_2171_, 0);
                leanh::lean_inc_ref(v_env_2178_);
                leanh::lean_dec(v___x_2171_);
                v___x_2179_ = leanh::lean_box(0);
                v___x_2180_ = lean_array_to_list(v_params_2174_);
                v___x_2181_ = l_Lean_Meta_nativeEqTrue___closed__5;
                leanh::lean_inc(v_tacticName_2148_);
                v___x_2182_ = l_Lean_Name_append(v___x_2181_, v_tacticName_2148_);
                v___x_2183_ = l_Lean_Meta_nativeEqTrue___closed__7;
                leanh::lean_inc(v___x_2182_);
                v___x_2184_ = l_Lean_Name_append(v___x_2182_, v___x_2183_);
                leanh::lean_inc(v_a_2165_);
                leanh::lean_inc(v___x_2180_);
                v___f_2185_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_nativeEqTrue___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    5,
                );
                leanh::lean_closure_set(v___f_2185_, 0, v___x_2184_);
                leanh::lean_closure_set(v___f_2185_, 1, v___x_2180_);
                leanh::lean_closure_set(v___f_2185_, 2, v___x_2179_);
                leanh::lean_closure_set(v___f_2185_, 3, v_tacticName_2148_);
                leanh::lean_closure_set(v___f_2185_, 4, v_a_2165_);
                v___x_2186_ = l_Lean_Environment_unlockAsync(v_env_2178_);
                v___x_2187_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
                    v___x_2186_,
                    v___f_2185_,
                    v___y_2167_,
                    v___y_2168_,
                    v___y_2169_,
                    v___y_2170_,
                );
                if leanh::lean_obj_tag(v___x_2187_) == 0 {
                    v_a_2188_ = leanh::lean_ctor_get(v___x_2187_, 0);
                    v_isSharedCheck_2237_ = (!leanh::lean_is_exclusive(v___x_2187_)) as u8;
                    if v_isSharedCheck_2237_ == 0 {
                        v___x_2190_ = v___x_2187_;
                        v_isShared_2191_ = v_isSharedCheck_2237_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2188_);
                        leanh::lean_dec(v___x_2187_);
                        v___x_2190_ = leanh::lean_box(0);
                        v_isShared_2191_ = v_isSharedCheck_2237_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2182_);
                    leanh::lean_dec(v___x_2180_);
                    leanh::lean_del_object(v___x_2176_);
                    leanh::lean_dec(v_a_2165_);
                    v_a_2238_ = leanh::lean_ctor_get(v___x_2187_, 0);
                    v_isSharedCheck_2245_ = (!leanh::lean_is_exclusive(v___x_2187_)) as u8;
                    if v_isSharedCheck_2245_ == 0 {
                        v___x_2240_ = v___x_2187_;
                        v_isShared_2241_ = v_isSharedCheck_2245_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2238_);
                        leanh::lean_dec(v___x_2187_);
                        v___x_2240_ = leanh::lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2245_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2192_ = (leanh::lean_unbox(v_a_2188_) as u8);
                leanh::lean_dec(v_a_2188_);
                if v___x_2192_ == 0 {
                    leanh::lean_dec(v___x_2182_);
                    leanh::lean_dec(v___x_2180_);
                    leanh::lean_del_object(v___x_2176_);
                    leanh::lean_dec(v_a_2165_);
                    v___x_2193_ = leanh::lean_box(1);
                    if v_isShared_2191_ == 0 {
                        leanh::lean_ctor_set(v___x_2190_, 0, v___x_2193_);
                        v___x_2195_ = v___x_2190_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2196_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
                        v___x_2195_ = v_reuseFailAlloc_2196_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2190_);
                    v___x_2197_ = l_Lean_Meta_nativeEqTrue___closed__9;
                    v___x_2198_ = l_Lean_Name_append(v___x_2182_, v___x_2197_);
                    v___x_2199_ =
                        l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
                            v___x_2198_,
                            v___y_2170_,
                        );
                    v_a_2200_ = leanh::lean_ctor_get(v___x_2199_, 0);
                    v_isSharedCheck_2236_ = (!leanh::lean_is_exclusive(v___x_2199_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2202_ = v___x_2199_;
                        v_isShared_2203_ = v_isSharedCheck_2236_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2200_);
                        leanh::lean_dec(v___x_2199_);
                        v___x_2202_ = leanh::lean_box(0);
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
                v___x_2204_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__14_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__14,
                );
                v___x_2205_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__15_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__15,
                );
                v___x_2206_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__18_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__18,
                );
                v___x_2207_ = l_Lean_mkApp3(v___x_2204_, v___x_2205_, v_a_2165_, v___x_2206_);
                leanh::lean_inc(v___x_2180_);
                leanh::lean_inc(v_a_2200_);
                if v_isShared_2177_ == 0 {
                    leanh::lean_ctor_set(v___x_2176_, 2, v___x_2207_);
                    leanh::lean_ctor_set(v___x_2176_, 1, v___x_2180_);
                    leanh::lean_ctor_set(v___x_2176_, 0, v_a_2200_);
                    v___x_2209_ = v___x_2176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2180_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 2, v___x_2207_);
                    v___x_2209_ = v_reuseFailAlloc_2235_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2210_ = 0;
                v___x_2211_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2211_, 0, v___x_2209_);
                leanh::lean_ctor_set_uint8(
                    v___x_2211_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2210_,
                );
                if v_isShared_2203_ == 0 {
                    leanh::lean_ctor_set(v___x_2202_, 0, v___x_2211_);
                    v___x_2213_ = v___x_2202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2211_);
                    v___x_2213_ = v_reuseFailAlloc_2234_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2214_ = l_Lean_addDecl(v___x_2213_, v___x_2210_, v___y_2169_, v___y_2170_);
                if leanh::lean_obj_tag(v___x_2214_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2214_, 1);
                    if leanh::lean_obj_tag(v_axiomDeclRange_x3f_2150_) == 1 {
                        v_val_2215_ = leanh::lean_ctor_get(v_axiomDeclRange_x3f_2150_, 0);
                        v___x_2216_ = leanh::lean_box(0);
                        leanh::lean_inc(v_a_2200_);
                        v___x_2217_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_a_2200_, v_val_2215_, v___x_2216_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
                        if leanh::lean_obj_tag(v___x_2217_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2217_, 1);
                            v___y_2157_ = v_a_2200_;
                            v___y_2158_ = v___x_2180_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2200_);
                            leanh::lean_dec(v___x_2180_);
                            v_a_2218_ = leanh::lean_ctor_get(v___x_2217_, 0);
                            v_isSharedCheck_2225_ =
                                (!leanh::lean_is_exclusive(v___x_2217_)) as u8;
                            if v_isSharedCheck_2225_ == 0 {
                                v___x_2220_ = v___x_2217_;
                                v_isShared_2221_ = v_isSharedCheck_2225_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2218_);
                                leanh::lean_dec(v___x_2217_);
                                v___x_2220_ = leanh::lean_box(0);
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
                    leanh::lean_dec(v_a_2200_);
                    leanh::lean_dec(v___x_2180_);
                    v_a_2226_ = leanh::lean_ctor_get(v___x_2214_, 0);
                    v_isSharedCheck_2233_ = (!leanh::lean_is_exclusive(v___x_2214_)) as u8;
                    if v_isSharedCheck_2233_ == 0 {
                        v___x_2228_ = v___x_2214_;
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2226_);
                        leanh::lean_dec(v___x_2214_);
                        v___x_2228_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
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
                    v_reuseFailAlloc_2232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
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
                    v_reuseFailAlloc_2244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
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
                    v___x_2255_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_2256_ = l_Lean_MessageData_ofName(v_tacticName_2148_);
                    v___x_2257_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2257_, 0, v___x_2255_);
                    leanh::lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                    v___x_2258_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__20),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__20_once),
                        _init_l_Lean_Meta_nativeEqTrue___closed__20,
                    );
                    v___x_2259_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2259_, 0, v___x_2257_);
                    leanh::lean_ctor_set(v___x_2259_, 1, v___x_2258_);
                    v___x_2260_ = l_Lean_indentExpr(v_a_2165_);
                    v___x_2261_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2261_, 0, v___x_2259_);
                    leanh::lean_ctor_set(v___x_2261_, 1, v___x_2260_);
                    v___x_2262_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2261_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
                    v_a_2263_ = leanh::lean_ctor_get(v___x_2262_, 0);
                    v_isSharedCheck_2270_ = (!leanh::lean_is_exclusive(v___x_2262_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v___x_2265_ = v___x_2262_;
                        v_isShared_2266_ = v_isSharedCheck_2270_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2263_);
                        leanh::lean_dec(v___x_2262_);
                        v___x_2265_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
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
                    v_reuseFailAlloc_2286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
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
    mut v_tacticName_2288_: *mut leanh::LeanObject,
    mut v_e_2289_: *mut leanh::LeanObject,
    mut v_axiomDeclRange_x3f_2290_: *mut leanh::LeanObject,
    mut v_a_2291_: *mut leanh::LeanObject,
    mut v_a_2292_: *mut leanh::LeanObject,
    mut v_a_2293_: *mut leanh::LeanObject,
    mut v_a_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Lean_Meta_nativeEqTrue(
        v_tacticName_2288_,
        v_e_2289_,
        v_axiomDeclRange_x3f_2290_,
        v_a_2291_,
        v_a_2292_,
        v_a_2293_,
        v_a_2294_,
    );
    leanh::lean_dec(v_a_2294_);
    leanh::lean_dec_ref(v_a_2293_);
    leanh::lean_dec(v_a_2292_);
    leanh::lean_dec_ref(v_a_2291_);
    leanh::lean_dec(v_axiomDeclRange_x3f_2290_);
    return v_res_2296_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(
    mut v_env_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2297_, v___y_2299_, v___y_2301_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(
    mut v_env_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2310_ =
        l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(
            v_env_2304_,
            v___y_2305_,
            v___y_2306_,
            v___y_2307_,
            v___y_2308_,
        );
    leanh::lean_dec(v___y_2308_);
    leanh::lean_dec_ref(v___y_2307_);
    leanh::lean_dec(v___y_2306_);
    leanh::lean_dec_ref(v___y_2305_);
    return v_res_2310_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(
    mut v_00_u03b1_2311_: *mut leanh::LeanObject,
    mut v_env_2312_: *mut leanh::LeanObject,
    mut v_x_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
    mut v___y_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2320_: *mut leanh::LeanObject,
    mut v_env_2321_: *mut leanh::LeanObject,
    mut v_x_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: *mut leanh::LeanObject,
    mut v___y_2327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(
        v_00_u03b1_2320_,
        v_env_2321_,
        v_x_2322_,
        v___y_2323_,
        v___y_2324_,
        v___y_2325_,
        v___y_2326_,
    );
    leanh::lean_dec(v___y_2326_);
    leanh::lean_dec_ref(v___y_2325_);
    leanh::lean_dec(v___y_2324_);
    leanh::lean_dec_ref(v___y_2323_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(
    mut v_stx_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_2329_, v___y_2332_);
    return v___x_2335_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(
    mut v_stx_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2342_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(v_stx_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
    leanh::lean_dec(v___y_2340_);
    leanh::lean_dec_ref(v___y_2339_);
    leanh::lean_dec(v___y_2338_);
    leanh::lean_dec_ref(v___y_2337_);
    leanh::lean_dec(v_stx_2336_);
    return v_res_2342_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(
    mut v_declName_2343_: *mut leanh::LeanObject,
    mut v_declRanges_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2350_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_2343_, v_declRanges_2344_, v___y_2346_, v___y_2348_);
    return v___x_2350_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(
    mut v_declName_2351_: *mut leanh::LeanObject,
    mut v_declRanges_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(v_declName_2351_, v_declRanges_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
    leanh::lean_dec(v___y_2356_);
    leanh::lean_dec_ref(v___y_2355_);
    leanh::lean_dec(v___y_2354_);
    leanh::lean_dec_ref(v___y_2353_);
    return v_res_2358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Native(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Native(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Native(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Native(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Native(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Native(builtin);
}