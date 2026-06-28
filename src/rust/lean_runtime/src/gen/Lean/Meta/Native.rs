// Lean compiler output
// Module: Lean.Meta.Native
// Imports: Lean.Meta.Basic Lean.Util.CollectLevelParams Lean.Elab.DeclarationRange Lean.Compiler.Options
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::MonadEnv::lean_has_compile_error;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_5, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value: LeanStringObject<9> =
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
        m_data: [84, 97, 99, 116, 105, 99, 32, 96, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value: LeanStringObject<57> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value: LeanStringObject<18> =
    LeanStringObject {
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
            96, 32, 102, 97, 105, 108, 101, 100, 46, 32, 69, 114, 114, 111, 114, 58, 32, 0,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value: LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___lam__0___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__2_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__4_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__4_value) as *mut LeanObject,
        12194354677470204327 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_nativeEqTrue___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__6_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__6_value) as *mut LeanObject,
        13787886431423481210 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_nativeEqTrue___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__8_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__8_value) as *mut LeanObject,
        16160311484268338767 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_nativeEqTrue___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__10_value: LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__10_value) as *mut LeanObject;
pub static l_Lean_Meta_nativeEqTrue___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__10_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_nativeEqTrue___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__11_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_nativeEqTrue___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__16_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Meta_nativeEqTrue___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__16_value) as *mut LeanObject;
static l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_nativeEqTrue___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__16_value) as *mut LeanObject,
        9255189395584251158 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_nativeEqTrue___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__17_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__19_value: LeanStringObject<63> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 67, 97, 110, 110, 111, 116, 32, 110, 97, 116,
        105, 118, 101, 32, 100, 101, 99, 105, 100, 101, 32, 112, 114, 111, 112, 111, 115, 105, 116,
        105, 111, 110, 32, 119, 105, 116, 104, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98,
        108, 101, 115, 58, 0,
    ],
};
static mut l_Lean_Meta_nativeEqTrue___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__19_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_nativeEqTrue___closed__21_value: LeanStringObject<64> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 64,
    m_capacity: 64,
    m_length: 63,
    m_data: [
        96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 67, 97, 110, 110, 111, 116, 32, 110, 97, 116,
        105, 118, 101, 32, 100, 101, 99, 105, 100, 101, 32, 112, 114, 111, 112, 111, 115, 105, 116,
        105, 111, 110, 32, 119, 105, 116, 104, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97,
        98, 108, 101, 115, 58, 0,
    ],
};
static mut l_Lean_Meta_nativeEqTrue___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_nativeEqTrue___closed__21_value) as *mut LeanObject;
static mut l_Lean_Meta_nativeEqTrue___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_nativeEqTrue___closed__22: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorIdx(
    mut v_x_1180_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1180_) == 0 {
        let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
        v___x_1181_ = lean_unsigned_to_nat(0);
        return v___x_1181_;
    } else {
        let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
        v___x_1182_ = lean_unsigned_to_nat(1);
        return v___x_1182_;
    }
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(
    mut v_x_1183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1184_: *mut LeanObject = core::ptr::null_mut();
    v_res_1184_ = l_Lean_Meta_NativeEqTrueResult_ctorIdx(v_x_1183_);
    lean_dec(v_x_1183_);
    return v_res_1184_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(
    mut v_t_1185_: *mut LeanObject,
    mut v_k_1186_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1185_) == 0 {
        let mut v_prf_1187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
        v_prf_1187_ = lean_ctor_get(v_t_1185_, 0);
        lean_inc_ref(v_prf_1187_);
        lean_dec_ref_known(v_t_1185_, 1);
        v___x_1188_ = lean_apply_1(v_k_1186_, v_prf_1187_);
        return v___x_1188_;
    } else {
        return v_k_1186_;
    }
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim(
    mut v_motive_1189_: *mut LeanObject,
    mut v_ctorIdx_1190_: *mut LeanObject,
    mut v_t_1191_: *mut LeanObject,
    mut v_h_1192_: *mut LeanObject,
    mut v_k_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    v___x_1194_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1191_, v_k_1193_);
    return v___x_1194_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(
    mut v_motive_1195_: *mut LeanObject,
    mut v_ctorIdx_1196_: *mut LeanObject,
    mut v_t_1197_: *mut LeanObject,
    mut v_h_1198_: *mut LeanObject,
    mut v_k_1199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1200_: *mut LeanObject = core::ptr::null_mut();
    v_res_1200_ = l_Lean_Meta_NativeEqTrueResult_ctorElim(
        v_motive_1195_,
        v_ctorIdx_1196_,
        v_t_1197_,
        v_h_1198_,
        v_k_1199_,
    );
    lean_dec(v_ctorIdx_1196_);
    return v_res_1200_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(
    mut v_t_1201_: *mut LeanObject,
    mut v_success_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1201_, v_success_1202_);
    return v___x_1203_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_success_elim(
    mut v_motive_1204_: *mut LeanObject,
    mut v_t_1205_: *mut LeanObject,
    mut v_h_1206_: *mut LeanObject,
    mut v_success_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1205_, v_success_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(
    mut v_t_1209_: *mut LeanObject,
    mut v_notTrue_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    v___x_1211_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1209_, v_notTrue_1210_);
    return v___x_1211_;
}
pub unsafe fn l_Lean_Meta_NativeEqTrueResult_notTrue_elim(
    mut v_motive_1212_: *mut LeanObject,
    mut v_t_1213_: *mut LeanObject,
    mut v_h_1214_: *mut LeanObject,
    mut v_notTrue_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_1213_, v_notTrue_1215_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    v___x_1217_ = lean_box(0);
    v___x_1218_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_1219_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1219_, 0, v___x_1218_);
    lean_ctor_set(v___x_1219_, 1, v___x_1217_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg()
-> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0);
    v___x_1222_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1222_, 0, v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___boxed(
    mut v___y_1223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1224_: *mut LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
    return v_res_1224_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(
    mut v_msgData_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    v___x_1231_ = lean_st_ref_get(v___y_1229_);
    v_env_1232_ = lean_ctor_get(v___x_1231_, 0);
    lean_inc_ref(v_env_1232_);
    lean_dec(v___x_1231_);
    v___x_1233_ = lean_st_ref_get(v___y_1227_);
    v_mctx_1234_ = lean_ctor_get(v___x_1233_, 0);
    lean_inc_ref(v_mctx_1234_);
    lean_dec(v___x_1233_);
    v_lctx_1235_ = lean_ctor_get(v___y_1226_, 2);
    v_options_1236_ = lean_ctor_get(v___y_1228_, 2);
    lean_inc_ref(v_options_1236_);
    lean_inc_ref(v_lctx_1235_);
    v___x_1237_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1237_, 0, v_env_1232_);
    lean_ctor_set(v___x_1237_, 1, v_mctx_1234_);
    lean_ctor_set(v___x_1237_, 2, v_lctx_1235_);
    lean_ctor_set(v___x_1237_, 3, v_options_1236_);
    v___x_1238_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    lean_ctor_set(v___x_1238_, 1, v_msgData_1225_);
    v___x_1239_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    return v___x_1239_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1246_: *mut LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
    lean_dec(v___y_1244_);
    lean_dec_ref(v___y_1243_);
    lean_dec(v___y_1242_);
    lean_dec_ref(v___y_1241_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(
    mut v_msg_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1253_ = lean_ctor_get(v___y_1250_, 5);
                v___x_1254_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
                v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
                v_isSharedCheck_1263_ = (!lean_is_exclusive(v___x_1254_)) as u8;
                if v_isSharedCheck_1263_ == 0 {
                    v___x_1257_ = v___x_1254_;
                    v_isShared_1258_ = v_isSharedCheck_1263_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1255_);
                    lean_dec(v___x_1254_);
                    v___x_1257_ = lean_box(0);
                    v_isShared_1258_ = v_isSharedCheck_1263_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1253_);
                v___x_1259_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1259_, 0, v_ref_1253_);
                lean_ctor_set(v___x_1259_, 1, v_a_1255_);
                if v_isShared_1258_ == 0 {
                    lean_ctor_set_tag(v___x_1257_, 1);
                    lean_ctor_set(v___x_1257_, 0, v___x_1259_);
                    v___x_1261_ = v___x_1257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
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
    mut v_msg_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
    lean_dec(v___y_1268_);
    lean_dec_ref(v___y_1267_);
    lean_dec(v___y_1266_);
    lean_dec_ref(v___y_1265_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(
    mut v_x_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1283_: u8 = 0;
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1271_) == 0 {
                    v_a_1277_ = lean_ctor_get(v_x_1271_, 0);
                    lean_inc(v_a_1277_);
                    lean_dec_ref_known(v_x_1271_, 1);
                    v___x_1278_ = l_Lean_stringToMessageData(v_a_1277_);
                    v___x_1279_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1278_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
                    return v___x_1279_;
                } else {
                    v_a_1280_ = lean_ctor_get(v_x_1271_, 0);
                    v_isSharedCheck_1287_ = (!lean_is_exclusive(v_x_1271_)) as u8;
                    if v_isSharedCheck_1287_ == 0 {
                        v___x_1282_ = v_x_1271_;
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1280_);
                        lean_dec(v_x_1271_);
                        v___x_1282_ = lean_box(0);
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1283_ == 0 {
                    lean_ctor_set_tag(v___x_1282_, 0);
                    v___x_1285_ = v___x_1282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
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
    mut v_x_1288_: *mut LeanObject,
    mut v___y_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1294_: *mut LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
    lean_dec(v___y_1292_);
    lean_dec_ref(v___y_1291_);
    lean_dec(v___y_1290_);
    lean_dec_ref(v___y_1289_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(
    mut v_constName_1295_: *mut LeanObject,
    mut v_checkMeta_1296_: u8,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1302_ = lean_st_ref_get(v___y_1300_);
                v_env_1303_ = lean_ctor_get(v___x_1302_, 0);
                lean_inc_ref(v_env_1303_);
                lean_dec(v___x_1302_);
                lean_inc(v_constName_1295_);
                v___x_1304_ = lean_has_compile_error(v_env_1303_, v_constName_1295_);
                if v___x_1304_ == 0 {
                    v___x_1305_ = lean_st_ref_get(v___y_1300_);
                    v_env_1306_ = lean_ctor_get(v___x_1305_, 0);
                    lean_inc_ref(v_env_1306_);
                    lean_dec(v___x_1305_);
                    v_options_1307_ = lean_ctor_get(v___y_1299_, 2);
                    v___x_1308_ = l_Lean_Environment_evalConst___redArg(
                        v_env_1306_,
                        v_options_1307_,
                        v_constName_1295_,
                        v_checkMeta_1296_,
                    );
                    lean_dec(v_constName_1295_);
                    lean_dec_ref(v_env_1306_);
                    v___x_1309_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_1308_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
                    return v___x_1309_;
                } else {
                    v___x_1310_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
                    if lean_obj_tag(v___x_1310_) == 0 {
                        lean_dec_ref_known(v___x_1310_, 1);
                        v___x_1311_ = lean_st_ref_get(v___y_1300_);
                        v_env_1312_ = lean_ctor_get(v___x_1311_, 0);
                        lean_inc_ref(v_env_1312_);
                        lean_dec(v___x_1311_);
                        v_options_1313_ = lean_ctor_get(v___y_1299_, 2);
                        v___x_1314_ = l_Lean_Environment_evalConst___redArg(
                            v_env_1312_,
                            v_options_1313_,
                            v_constName_1295_,
                            v_checkMeta_1296_,
                        );
                        lean_dec(v_constName_1295_);
                        lean_dec_ref(v_env_1312_);
                        v___x_1315_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_1314_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
                        return v___x_1315_;
                    } else {
                        lean_dec(v_constName_1295_);
                        v_a_1316_ = lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1323_ = (!lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1323_ == 0 {
                            v___x_1318_ = v___x_1310_;
                            v_isShared_1319_ = v_isSharedCheck_1323_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1316_);
                            lean_dec(v___x_1310_);
                            v___x_1318_ = lean_box(0);
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
                    v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
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
    mut v_constName_1324_: *mut LeanObject,
    mut v_checkMeta_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_1331_: u8 = 0;
    let mut v_res_1332_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1331_ = (lean_unbox(v_checkMeta_1325_) as u8);
    v_res_1332_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_1324_, v_checkMeta_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
    lean_dec(v___y_1329_);
    lean_dec_ref(v___y_1328_);
    lean_dec(v___y_1327_);
    lean_dec_ref(v___y_1326_);
    return v_res_1332_;
}
pub unsafe fn l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
    mut v_auxDeclName_1333_: *mut LeanObject,
    mut v_a_1334_: *mut LeanObject,
    mut v_a_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
    mut v_a_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1339_: u8 = 0;
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    v___x_1339_ = 1;
    v___x_1340_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_auxDeclName_1333_, v___x_1339_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
    return v___x_1340_;
}
pub unsafe fn l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(
    mut v_auxDeclName_1341_: *mut LeanObject,
    mut v_a_1342_: *mut LeanObject,
    mut v_a_1343_: *mut LeanObject,
    mut v_a_1344_: *mut LeanObject,
    mut v_a_1345_: *mut LeanObject,
    mut v_a_1346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1347_: *mut LeanObject = core::ptr::null_mut();
    v_res_1347_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
        v_auxDeclName_1341_,
        v_a_1342_,
        v_a_1343_,
        v_a_1344_,
        v_a_1345_,
    );
    lean_dec(v_a_1345_);
    lean_dec_ref(v_a_1344_);
    lean_dec(v_a_1343_);
    lean_dec_ref(v_a_1342_);
    return v_res_1347_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(
    mut v_00_u03b1_1348_: *mut LeanObject,
    mut v___y_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
    mut v___y_1351_: *mut LeanObject,
    mut v___y_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
    return v___x_1354_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___boxed(
    mut v_00_u03b1_1355_: *mut LeanObject,
    mut v___y_1356_: *mut LeanObject,
    mut v___y_1357_: *mut LeanObject,
    mut v___y_1358_: *mut LeanObject,
    mut v___y_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1361_: *mut LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(v_00_u03b1_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
    lean_dec(v___y_1359_);
    lean_dec_ref(v___y_1358_);
    lean_dec(v___y_1357_);
    lean_dec_ref(v___y_1356_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(
    mut v_00_u03b1_1362_: *mut LeanObject,
    mut v_constName_1363_: *mut LeanObject,
    mut v_checkMeta_1364_: u8,
    mut v___y_1365_: *mut LeanObject,
    mut v___y_1366_: *mut LeanObject,
    mut v___y_1367_: *mut LeanObject,
    mut v___y_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_1363_, v_checkMeta_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
    return v___x_1370_;
}
pub unsafe fn l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___boxed(
    mut v_00_u03b1_1371_: *mut LeanObject,
    mut v_constName_1372_: *mut LeanObject,
    mut v_checkMeta_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
    mut v___y_1375_: *mut LeanObject,
    mut v___y_1376_: *mut LeanObject,
    mut v___y_1377_: *mut LeanObject,
    mut v___y_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checkMeta_boxed_1379_: u8 = 0;
    let mut v_res_1380_: *mut LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1379_ = (lean_unbox(v_checkMeta_1373_) as u8);
    v_res_1380_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(v_00_u03b1_1371_, v_constName_1372_, v_checkMeta_boxed_1379_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
    lean_dec(v___y_1377_);
    lean_dec_ref(v___y_1376_);
    lean_dec(v___y_1375_);
    lean_dec_ref(v___y_1374_);
    return v_res_1380_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(
    mut v_00_u03b1_1381_: *mut LeanObject,
    mut v_x_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
    return v___x_1388_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___boxed(
    mut v_00_u03b1_1389_: *mut LeanObject,
    mut v_x_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
    mut v___y_1394_: *mut LeanObject,
    mut v___y_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1396_: *mut LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(v_00_u03b1_1389_, v_x_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
    lean_dec(v___y_1394_);
    lean_dec_ref(v___y_1393_);
    lean_dec(v___y_1392_);
    lean_dec_ref(v___y_1391_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1397_: *mut LeanObject,
    mut v_msg_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
    mut v___y_1400_: *mut LeanObject,
    mut v___y_1401_: *mut LeanObject,
    mut v___y_1402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1405_: *mut LeanObject,
    mut v_msg_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1412_: *mut LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_1405_, v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
    lean_dec(v___y_1410_);
    lean_dec_ref(v___y_1409_);
    lean_dec(v___y_1408_);
    lean_dec_ref(v___y_1407_);
    return v_res_1412_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
    mut v_e_1413_: *mut LeanObject,
    mut v___y_1414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1416_: u8 = 0;
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_unused_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1416_ = l_Lean_Expr_hasMVar(v_e_1413_);
                if v___x_1416_ == 0 {
                    v___x_1417_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1417_, 0, v_e_1413_);
                    return v___x_1417_;
                } else {
                    v___x_1418_ = lean_st_ref_get(v___y_1414_);
                    v_mctx_1419_ = lean_ctor_get(v___x_1418_, 0);
                    lean_inc_ref(v_mctx_1419_);
                    lean_dec(v___x_1418_);
                    v___x_1420_ = l_Lean_instantiateMVarsCore(v_mctx_1419_, v_e_1413_);
                    v_fst_1421_ = lean_ctor_get(v___x_1420_, 0);
                    lean_inc(v_fst_1421_);
                    v_snd_1422_ = lean_ctor_get(v___x_1420_, 1);
                    lean_inc(v_snd_1422_);
                    lean_dec_ref(v___x_1420_);
                    v___x_1423_ = lean_st_ref_take(v___y_1414_);
                    v_cache_1424_ = lean_ctor_get(v___x_1423_, 1);
                    v_zetaDeltaFVarIds_1425_ = lean_ctor_get(v___x_1423_, 2);
                    v_postponed_1426_ = lean_ctor_get(v___x_1423_, 3);
                    v_diag_1427_ = lean_ctor_get(v___x_1423_, 4);
                    v_isSharedCheck_1436_ = (!lean_is_exclusive(v___x_1423_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v_unused_1437_ = lean_ctor_get(v___x_1423_, 0);
                        lean_dec(v_unused_1437_);
                        v___x_1429_ = v___x_1423_;
                        v_isShared_1430_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1427_);
                        lean_inc(v_postponed_1426_);
                        lean_inc(v_zetaDeltaFVarIds_1425_);
                        lean_inc(v_cache_1424_);
                        lean_dec(v___x_1423_);
                        v___x_1429_ = lean_box(0);
                        v_isShared_1430_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1430_ == 0 {
                    lean_ctor_set(v___x_1429_, 0, v_snd_1422_);
                    v___x_1432_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_snd_1422_);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_cache_1424_);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_zetaDeltaFVarIds_1425_);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_postponed_1426_);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_diag_1427_);
                    v___x_1432_ = v_reuseFailAlloc_1435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1433_ = lean_st_ref_set(v___y_1414_, v___x_1432_);
                v___x_1434_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1434_, 0, v_fst_1421_);
                return v___x_1434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(
    mut v_e_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
    mut v___y_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1441_: *mut LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
        v_e_1438_,
        v___y_1439_,
    );
    lean_dec(v___y_1439_);
    return v_res_1441_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(
    mut v_e_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    v___x_1448_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
        v_e_1442_,
        v___y_1444_,
    );
    return v___x_1448_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(
    mut v_e_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1455_: *mut LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(
        v_e_1449_,
        v___y_1450_,
        v___y_1451_,
        v___y_1452_,
        v___y_1453_,
    );
    lean_dec(v___y_1453_);
    lean_dec_ref(v___y_1452_);
    lean_dec(v___y_1451_);
    lean_dec_ref(v___y_1450_);
    return v_res_1455_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
    mut v_kind_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut v_unused_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1459_ = lean_st_ref_get(v___y_1457_);
                v_auxDeclNGen_1460_ = lean_ctor_get(v___x_1459_, 3);
                lean_inc_ref(v_auxDeclNGen_1460_);
                lean_dec(v___x_1459_);
                v___x_1461_ = lean_st_ref_get(v___y_1457_);
                v_env_1462_ = lean_ctor_get(v___x_1461_, 0);
                lean_inc_ref(v_env_1462_);
                lean_dec(v___x_1461_);
                v___x_1463_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_1462_,
                    v_auxDeclNGen_1460_,
                    v_kind_1456_,
                );
                v_fst_1464_ = lean_ctor_get(v___x_1463_, 0);
                lean_inc(v_fst_1464_);
                v_snd_1465_ = lean_ctor_get(v___x_1463_, 1);
                lean_inc(v_snd_1465_);
                lean_dec_ref(v___x_1463_);
                v___x_1466_ = lean_st_ref_take(v___y_1457_);
                v_env_1467_ = lean_ctor_get(v___x_1466_, 0);
                v_nextMacroScope_1468_ = lean_ctor_get(v___x_1466_, 1);
                v_ngen_1469_ = lean_ctor_get(v___x_1466_, 2);
                v_traceState_1470_ = lean_ctor_get(v___x_1466_, 4);
                v_cache_1471_ = lean_ctor_get(v___x_1466_, 5);
                v_messages_1472_ = lean_ctor_get(v___x_1466_, 6);
                v_infoState_1473_ = lean_ctor_get(v___x_1466_, 7);
                v_snapshotTasks_1474_ = lean_ctor_get(v___x_1466_, 8);
                v_isSharedCheck_1483_ = (!lean_is_exclusive(v___x_1466_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v_unused_1484_ = lean_ctor_get(v___x_1466_, 3);
                    lean_dec(v_unused_1484_);
                    v___x_1476_ = v___x_1466_;
                    v_isShared_1477_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1474_);
                    lean_inc(v_infoState_1473_);
                    lean_inc(v_messages_1472_);
                    lean_inc(v_cache_1471_);
                    lean_inc(v_traceState_1470_);
                    lean_inc(v_ngen_1469_);
                    lean_inc(v_nextMacroScope_1468_);
                    lean_inc(v_env_1467_);
                    lean_dec(v___x_1466_);
                    v___x_1476_ = lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1477_ == 0 {
                    lean_ctor_set(v___x_1476_, 3, v_snd_1465_);
                    v___x_1479_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_env_1467_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_nextMacroScope_1468_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_ngen_1469_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_snd_1465_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_traceState_1470_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 5, v_cache_1471_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 6, v_messages_1472_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 7, v_infoState_1473_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 8, v_snapshotTasks_1474_);
                    v___x_1479_ = v_reuseFailAlloc_1482_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1480_ = lean_st_ref_set(v___y_1457_, v___x_1479_);
                v___x_1481_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1481_, 0, v_fst_1464_);
                return v___x_1481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(
    mut v_kind_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1488_: *mut LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
        v_kind_1485_,
        v___y_1486_,
    );
    lean_dec(v___y_1486_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(
    mut v_kind_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
    mut v___y_1491_: *mut LeanObject,
    mut v___y_1492_: *mut LeanObject,
    mut v___y_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
        v_kind_1489_,
        v___y_1493_,
    );
    return v___x_1495_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(
    mut v_kind_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
    mut v___y_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1502_: *mut LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(
        v_kind_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
        v___y_1500_,
    );
    lean_dec(v___y_1500_);
    lean_dec_ref(v___y_1499_);
    lean_dec(v___y_1498_);
    lean_dec_ref(v___y_1497_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(
    mut v_opts_1503_: *mut LeanObject,
    mut v_opt_1504_: *mut LeanObject,
) -> u8 {
    let mut v_name_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    v_name_1505_ = lean_ctor_get(v_opt_1504_, 0);
    v_defValue_1506_ = lean_ctor_get(v_opt_1504_, 1);
    v_map_1507_ = lean_ctor_get(v_opts_1503_, 0);
    v___x_1508_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1507_,
            v_name_1505_,
        );
    if lean_obj_tag(v___x_1508_) == 0 {
        let mut v___x_1509_: u8 = 0;
        v___x_1509_ = (lean_unbox(v_defValue_1506_) as u8);
        return v___x_1509_;
    } else {
        let mut v_val_1510_: *mut LeanObject = core::ptr::null_mut();
        v_val_1510_ = lean_ctor_get(v___x_1508_, 0);
        lean_inc(v_val_1510_);
        lean_dec_ref_known(v___x_1508_, 1);
        if lean_obj_tag(v_val_1510_) == 1 {
            let mut v_v_1511_: u8 = 0;
            v_v_1511_ = lean_ctor_get_uint8(v_val_1510_, 0 as u32);
            lean_dec_ref_known(v_val_1510_, 0);
            return v_v_1511_;
        } else {
            let mut v___x_1512_: u8 = 0;
            lean_dec(v_val_1510_);
            v___x_1512_ = (lean_unbox(v_defValue_1506_) as u8);
            return v___x_1512_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(
    mut v_opts_1513_: *mut LeanObject,
    mut v_opt_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut LeanObject = core::ptr::null_mut();
    v_res_1515_ =
        l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v_opts_1513_, v_opt_1514_);
    lean_dec_ref(v_opt_1514_);
    lean_dec_ref(v_opts_1513_);
    v_r_1516_ = lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
    mut v_opts_1517_: *mut LeanObject,
    mut v_opt_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    v_name_1519_ = lean_ctor_get(v_opt_1518_, 0);
    v_defValue_1520_ = lean_ctor_get(v_opt_1518_, 1);
    v_map_1521_ = lean_ctor_get(v_opts_1517_, 0);
    v___x_1522_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1521_,
            v_name_1519_,
        );
    if lean_obj_tag(v___x_1522_) == 0 {
        lean_inc(v_defValue_1520_);
        return v_defValue_1520_;
    } else {
        let mut v_val_1523_: *mut LeanObject = core::ptr::null_mut();
        v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
        lean_inc(v_val_1523_);
        lean_dec_ref_known(v___x_1522_, 1);
        if lean_obj_tag(v_val_1523_) == 3 {
            let mut v_v_1524_: *mut LeanObject = core::ptr::null_mut();
            v_v_1524_ = lean_ctor_get(v_val_1523_, 0);
            lean_inc(v_v_1524_);
            lean_dec_ref_known(v_val_1523_, 1);
            return v_v_1524_;
        } else {
            lean_dec(v_val_1523_);
            lean_inc(v_defValue_1520_);
            return v_defValue_1520_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(
    mut v_opts_1525_: *mut LeanObject,
    mut v_opt_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1527_: *mut LeanObject = core::ptr::null_mut();
    v_res_1527_ =
        l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_1525_, v_opt_1526_);
    lean_dec_ref(v_opt_1526_);
    lean_dec_ref(v_opts_1525_);
    return v_res_1527_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
    mut v_o_1531_: *mut LeanObject,
    mut v_k_1532_: *mut LeanObject,
    mut v_v_1533_: u8,
) -> *mut LeanObject {
    let mut v_map_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1535_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1534_ = lean_ctor_get(v_o_1531_, 0);
                v_hasTrace_1535_ = lean_ctor_get_uint8(
                    v_o_1531_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1549_ = (!lean_is_exclusive(v_o_1531_)) as u8;
                if v_isSharedCheck_1549_ == 0 {
                    v___x_1537_ = v_o_1531_;
                    v_isShared_1538_ = v_isSharedCheck_1549_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_1534_);
                    lean_dec(v_o_1531_);
                    v___x_1537_ = lean_box(0);
                    v_isShared_1538_ = v_isSharedCheck_1549_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1539_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_1539_, 0 as u32, v_v_1533_);
                lean_inc(v_k_1532_);
                v___x_1540_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1532_, v___x_1539_, v_map_1534_);
                if v_hasTrace_1535_ == 0 {
                    v___x_1541_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1;
                    v___x_1542_ = l_Lean_Name_isPrefixOf(v___x_1541_, v_k_1532_);
                    lean_dec(v_k_1532_);
                    if v_isShared_1538_ == 0 {
                        lean_ctor_set(v___x_1537_, 0, v___x_1540_);
                        v___x_1544_ = v___x_1537_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1540_);
                        v___x_1544_ = v_reuseFailAlloc_1545_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_1532_);
                    if v_isShared_1538_ == 0 {
                        lean_ctor_set(v___x_1537_, 0, v___x_1540_);
                        v___x_1547_ = v___x_1537_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1540_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1548_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_1535_,
                        );
                        v___x_1547_ = v_reuseFailAlloc_1548_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1544_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_o_1550_: *mut LeanObject,
    mut v_k_1551_: *mut LeanObject,
    mut v_v_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1553_: u8 = 0;
    let mut v_res_1554_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1553_ = (lean_unbox(v_v_1552_) as u8);
    v_res_1554_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
            v_o_1550_,
            v_k_1551_,
            v_v_boxed_1553_,
        );
    return v_res_1554_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
    mut v_opts_1555_: *mut LeanObject,
    mut v_opt_1556_: *mut LeanObject,
    mut v_val_1557_: u8,
) -> *mut LeanObject {
    let mut v_name_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    v_name_1558_ = lean_ctor_get(v_opt_1556_, 0);
    lean_inc(v_name_1558_);
    lean_dec_ref(v_opt_1556_);
    v___x_1559_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(
            v_opts_1555_,
            v_name_1558_,
            v_val_1557_,
        );
    return v___x_1559_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(
    mut v_opts_1560_: *mut LeanObject,
    mut v_opt_1561_: *mut LeanObject,
    mut v_val_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_1563_: u8 = 0;
    let mut v_res_1564_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_1563_ = (lean_unbox(v_val_1562_) as u8);
    v_res_1564_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(
        v_opts_1560_,
        v_opt_1561_,
        v_val_boxed_1563_,
    );
    return v_res_1564_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__0;
    v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__2;
    v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
    return v___x_1570_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    v___x_1572_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__4;
    v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    v___x_1577_ = lean_box(0);
    v___x_1578_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__7;
    v___x_1579_ = l_Lean_mkConst(v___x_1578_, v___x_1577_);
    return v___x_1579_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9() -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1580_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10() -> *mut LeanObject {
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    v___x_1581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9,
    );
    v___x_1582_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1582_, 0, v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11() -> *mut LeanObject {
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10,
    );
    v___x_1584_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1584_, 0, v___x_1583_);
    lean_ctor_set(v___x_1584_, 1, v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12() -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once),
        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10,
    );
    v___x_1586_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1586_, 0, v___x_1585_);
    lean_ctor_set(v___x_1586_, 1, v___x_1585_);
    lean_ctor_set(v___x_1586_, 2, v___x_1585_);
    lean_ctor_set(v___x_1586_, 3, v___x_1585_);
    lean_ctor_set(v___x_1586_, 4, v___x_1585_);
    lean_ctor_set(v___x_1586_, 5, v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn l_Lean_Meta_nativeEqTrue___lam__0(
    mut v___x_1587_: *mut LeanObject,
    mut v___x_1588_: *mut LeanObject,
    mut v___x_1589_: *mut LeanObject,
    mut v_tacticName_1590_: *mut LeanObject,
    mut v_a_1591_: *mut LeanObject,
    mut v___y_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: u8 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___y_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: u8 = 0;
    let mut v_a_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v___y_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: u8 = 0;
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: u8 = 0;
    let mut v___y_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: u8 = 0;
    let mut v___y_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1697_: u8 = 0;
    let mut v_inheritedTraceOptions_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: u8 = 0;
    let mut v___y_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1708_: u8 = 0;
    let mut v___y_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1723_: u8 = 0;
    let mut v_inheritedTraceOptions_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: u8 = 0;
    let mut v___y_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1731_: u8 = 0;
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut v_unused_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1755_: u8 = 0;
    let mut v___y_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1772_: u8 = 0;
    let mut v_inheritedTraceOptions_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v_env_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v_reuseFailAlloc_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut v_unused_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1791_: u8 = 0;
    let mut v___y_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1795_: u8 = 0;
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v_unused_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___y_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1831_: u8 = 0;
    let mut v_inheritedTraceOptions_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v_env_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u8 = 0;
    let mut v___x_1844_: u8 = 0;
    let mut v_reuseFailAlloc_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: u8 = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1868_: u8 = 0;
    let mut v_unused_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v_reuseFailAlloc_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_unused_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_unused_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1609_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
                    v___x_1587_,
                    v___y_1595_,
                );
                v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
                v_isSharedCheck_1878_ = (!lean_is_exclusive(v___x_1609_)) as u8;
                if v_isSharedCheck_1878_ == 0 {
                    v___x_1612_ = v___x_1609_;
                    v_isShared_1613_ = v_isSharedCheck_1878_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_1610_);
                    lean_dec(v___x_1609_);
                    v___x_1612_ = lean_box(0);
                    v_isShared_1613_ = v_isSharedCheck_1878_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1600_ == 0 {
                    lean_dec_ref(v___y_1599_);
                    v___x_1601_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_1602_ = l_Lean_MessageData_ofName(v_tacticName_1590_);
                    v___x_1603_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1603_, 0, v___x_1601_);
                    lean_ctor_set(v___x_1603_, 1, v___x_1602_);
                    v___x_1604_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3,
                    );
                    v___x_1605_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1605_, 0, v___x_1603_);
                    lean_ctor_set(v___x_1605_, 1, v___x_1604_);
                    v___x_1606_ = l_Lean_Exception_toMessageData(v___y_1598_);
                    v___x_1607_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1607_, 0, v___x_1605_);
                    lean_ctor_set(v___x_1607_, 1, v___x_1606_);
                    v___x_1608_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1607_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
                    lean_dec_ref(v___y_1594_);
                    return v___x_1608_;
                } else {
                    lean_dec_ref(v___y_1598_);
                    lean_dec_ref(v___y_1594_);
                    lean_dec(v_tacticName_1590_);
                    return v___y_1599_;
                }
            }
            2 => {
                v___x_1640_ = lean_st_ref_take(v___y_1595_);
                v_env_1641_ = lean_ctor_get(v___x_1640_, 0);
                v_nextMacroScope_1642_ = lean_ctor_get(v___x_1640_, 1);
                v_ngen_1643_ = lean_ctor_get(v___x_1640_, 2);
                v_auxDeclNGen_1644_ = lean_ctor_get(v___x_1640_, 3);
                v_traceState_1645_ = lean_ctor_get(v___x_1640_, 4);
                v_messages_1646_ = lean_ctor_get(v___x_1640_, 6);
                v_infoState_1647_ = lean_ctor_get(v___x_1640_, 7);
                v_snapshotTasks_1648_ = lean_ctor_get(v___x_1640_, 8);
                v_isSharedCheck_1876_ = (!lean_is_exclusive(v___x_1640_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v_unused_1877_ = lean_ctor_get(v___x_1640_, 5);
                    lean_dec(v_unused_1877_);
                    v___x_1650_ = v___x_1640_;
                    v_isShared_1651_ = v_isSharedCheck_1876_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1648_);
                    lean_inc(v_infoState_1647_);
                    lean_inc(v_messages_1646_);
                    lean_inc(v_traceState_1645_);
                    lean_inc(v_auxDeclNGen_1644_);
                    lean_inc(v_ngen_1643_);
                    lean_inc(v_nextMacroScope_1642_);
                    lean_inc(v_env_1641_);
                    lean_dec(v___x_1640_);
                    v___x_1650_ = lean_box(0);
                    v_isShared_1651_ = v_isSharedCheck_1876_;
                    state = 7;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v___y_1615_) == 0 {
                    lean_dec_ref_known(v___y_1615_, 1);
                    v___x_1616_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(
                        v_a_1610_,
                        v___y_1592_,
                        v___y_1593_,
                        v___y_1594_,
                        v___y_1595_,
                    );
                    if lean_obj_tag(v___x_1616_) == 0 {
                        lean_dec_ref(v___y_1594_);
                        lean_dec(v_tacticName_1590_);
                        return v___x_1616_;
                    } else {
                        v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
                        lean_inc(v_a_1617_);
                        v___x_1618_ = l_Lean_Exception_isInterrupt(v_a_1617_);
                        if v___x_1618_ == 0 {
                            lean_inc(v_a_1617_);
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
                    lean_dec(v_a_1610_);
                    lean_dec_ref(v___y_1594_);
                    lean_dec(v_tacticName_1590_);
                    v_a_1620_ = lean_ctor_get(v___y_1615_, 0);
                    v_isSharedCheck_1627_ = (!lean_is_exclusive(v___y_1615_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v___x_1622_ = v___y_1615_;
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1620_);
                        lean_dec(v___y_1615_);
                        v___x_1622_ = lean_box(0);
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
                    v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
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
                    lean_dec_ref(v___y_1630_);
                    v___x_1632_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    lean_inc(v_tacticName_1590_);
                    v___x_1633_ = l_Lean_MessageData_ofName(v_tacticName_1590_);
                    v___x_1634_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                    lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                    v___x_1635_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5,
                    );
                    v___x_1636_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1636_, 0, v___x_1634_);
                    lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                    v___x_1637_ = l_Lean_Exception_toMessageData(v___y_1629_);
                    v___x_1638_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1638_, 0, v___x_1636_);
                    lean_ctor_set(v___x_1638_, 1, v___x_1637_);
                    v___x_1639_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1638_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
                    v___y_1615_ = v___x_1639_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v___y_1629_);
                    v___y_1615_ = v___y_1630_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_1652_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8,
                );
                lean_inc_n(v_a_1610_, 3);
                v___x_1653_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1653_, 0, v_a_1610_);
                lean_ctor_set(v___x_1653_, 1, v___x_1588_);
                lean_ctor_set(v___x_1653_, 2, v___x_1652_);
                v___x_1654_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1654_, 0, v_a_1610_);
                lean_ctor_set(v___x_1654_, 1, v___x_1589_);
                v___x_1655_ = l_Lean_markMeta(v_env_1641_, v_a_1610_);
                v___x_1656_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_1651_ == 0 {
                    lean_ctor_set(v___x_1650_, 5, v___x_1656_);
                    lean_ctor_set(v___x_1650_, 0, v___x_1655_);
                    v___x_1658_ = v___x_1650_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1655_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_nextMacroScope_1642_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_ngen_1643_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_auxDeclNGen_1644_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_traceState_1645_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 5, v___x_1656_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 6, v_messages_1646_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 7, v_infoState_1647_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 8, v_snapshotTasks_1648_);
                    v___x_1658_ = v_reuseFailAlloc_1875_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1659_ = lean_st_ref_set(v___y_1595_, v___x_1658_);
                v___x_1660_ = lean_st_ref_take(v___y_1593_);
                v_mctx_1661_ = lean_ctor_get(v___x_1660_, 0);
                v_zetaDeltaFVarIds_1662_ = lean_ctor_get(v___x_1660_, 2);
                v_postponed_1663_ = lean_ctor_get(v___x_1660_, 3);
                v_diag_1664_ = lean_ctor_get(v___x_1660_, 4);
                v_isSharedCheck_1873_ = (!lean_is_exclusive(v___x_1660_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v_unused_1874_ = lean_ctor_get(v___x_1660_, 1);
                    lean_dec(v_unused_1874_);
                    v___x_1666_ = v___x_1660_;
                    v_isShared_1667_ = v_isSharedCheck_1873_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_diag_1664_);
                    lean_inc(v_postponed_1663_);
                    lean_inc(v_zetaDeltaFVarIds_1662_);
                    lean_inc(v_mctx_1661_);
                    lean_dec(v___x_1660_);
                    v___x_1666_ = lean_box(0);
                    v_isShared_1667_ = v_isSharedCheck_1873_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1668_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_1667_ == 0 {
                    lean_ctor_set(v___x_1666_, 1, v___x_1668_);
                    v___x_1670_ = v___x_1666_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_mctx_1661_);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1668_);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_zetaDeltaFVarIds_1662_);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_postponed_1663_);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_diag_1664_);
                    v___x_1670_ = v_reuseFailAlloc_1872_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1671_ = lean_st_ref_set(v___y_1593_, v___x_1670_);
                v___x_1672_ = lean_st_ref_get(v___y_1595_);
                v_options_1673_ = lean_ctor_get(v___y_1594_, 2);
                v_env_1674_ = lean_ctor_get(v___x_1672_, 0);
                lean_inc_ref(v_env_1674_);
                lean_dec(v___x_1672_);
                v___x_1675_ = lean_box(1);
                v___x_1676_ = 1;
                v___x_1677_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_1677_, 0, v___x_1653_);
                lean_ctor_set(v___x_1677_, 1, v_a_1591_);
                lean_ctor_set(v___x_1677_, 2, v___x_1675_);
                lean_ctor_set(v___x_1677_, 3, v___x_1654_);
                lean_ctor_set_uint8(
                    v___x_1677_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_1676_,
                );
                if v_isShared_1613_ == 0 {
                    lean_ctor_set_tag(v___x_1612_, 1);
                    lean_ctor_set(v___x_1612_, 0, v___x_1677_);
                    v___x_1679_ = v___x_1612_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1677_);
                    v___x_1679_ = v_reuseFailAlloc_1871_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1680_ = 1;
                v___x_1681_ = 0;
                v___x_1751_ = l_Lean_Elab_async;
                lean_inc_ref(v_options_1673_);
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
                lean_dec_ref(v_env_1674_);
                if v___x_1870_ == 0 {
                    if v___x_1815_ == 0 {
                        lean_inc_ref(v___y_1594_);
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
                v___x_1701_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1701_, 0, v_fileName_1686_);
                lean_ctor_set(v___x_1701_, 1, v_fileMap_1687_);
                lean_ctor_set(v___x_1701_, 2, v___y_1683_);
                lean_ctor_set(v___x_1701_, 3, v_currRecDepth_1688_);
                lean_ctor_set(v___x_1701_, 4, v___x_1700_);
                lean_ctor_set(v___x_1701_, 5, v_ref_1689_);
                lean_ctor_set(v___x_1701_, 6, v_currNamespace_1690_);
                lean_ctor_set(v___x_1701_, 7, v_openDecls_1691_);
                lean_ctor_set(v___x_1701_, 8, v_initHeartbeats_1692_);
                lean_ctor_set(v___x_1701_, 9, v_maxHeartbeats_1693_);
                lean_ctor_set(v___x_1701_, 10, v_quotContext_1694_);
                lean_ctor_set(v___x_1701_, 11, v_currMacroScope_1695_);
                lean_ctor_set(v___x_1701_, 12, v_cancelTk_x3f_1696_);
                lean_ctor_set(v___x_1701_, 13, v_inheritedTraceOptions_1698_);
                lean_ctor_set_uint8(
                    v___x_1701_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_1684_,
                );
                lean_ctor_set_uint8(
                    v___x_1701_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1697_,
                );
                v___x_1702_ = l_Lean_addAndCompile(
                    v___x_1679_,
                    v___x_1680_,
                    v___x_1681_,
                    v___x_1701_,
                    v___y_1699_,
                );
                lean_dec_ref_known(v___x_1701_, 14);
                if lean_obj_tag(v___x_1702_) == 0 {
                    v___y_1615_ = v___x_1702_;
                    state = 3;
                    continue;
                } else {
                    v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
                    lean_inc(v_a_1703_);
                    v___x_1704_ = l_Lean_Exception_isInterrupt(v_a_1703_);
                    if v___x_1704_ == 0 {
                        lean_inc(v_a_1703_);
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
                v_fileName_1712_ = lean_ctor_get(v___y_1710_, 0);
                lean_inc_ref(v_fileName_1712_);
                v_fileMap_1713_ = lean_ctor_get(v___y_1710_, 1);
                lean_inc_ref(v_fileMap_1713_);
                v_currRecDepth_1714_ = lean_ctor_get(v___y_1710_, 3);
                lean_inc(v_currRecDepth_1714_);
                v_ref_1715_ = lean_ctor_get(v___y_1710_, 5);
                lean_inc(v_ref_1715_);
                v_currNamespace_1716_ = lean_ctor_get(v___y_1710_, 6);
                lean_inc(v_currNamespace_1716_);
                v_openDecls_1717_ = lean_ctor_get(v___y_1710_, 7);
                lean_inc(v_openDecls_1717_);
                v_initHeartbeats_1718_ = lean_ctor_get(v___y_1710_, 8);
                lean_inc(v_initHeartbeats_1718_);
                v_maxHeartbeats_1719_ = lean_ctor_get(v___y_1710_, 9);
                lean_inc(v_maxHeartbeats_1719_);
                v_quotContext_1720_ = lean_ctor_get(v___y_1710_, 10);
                lean_inc(v_quotContext_1720_);
                v_currMacroScope_1721_ = lean_ctor_get(v___y_1710_, 11);
                lean_inc(v_currMacroScope_1721_);
                v_cancelTk_x3f_1722_ = lean_ctor_get(v___y_1710_, 12);
                lean_inc(v_cancelTk_x3f_1722_);
                v_suppressElabErrors_1723_ = lean_ctor_get_uint8(
                    v___y_1710_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1724_ = lean_ctor_get(v___y_1710_, 13);
                lean_inc_ref(v_inheritedTraceOptions_1724_);
                lean_dec_ref(v___y_1710_);
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
                    v_env_1733_ = lean_ctor_get(v___x_1732_, 0);
                    v_nextMacroScope_1734_ = lean_ctor_get(v___x_1732_, 1);
                    v_ngen_1735_ = lean_ctor_get(v___x_1732_, 2);
                    v_auxDeclNGen_1736_ = lean_ctor_get(v___x_1732_, 3);
                    v_traceState_1737_ = lean_ctor_get(v___x_1732_, 4);
                    v_messages_1738_ = lean_ctor_get(v___x_1732_, 6);
                    v_infoState_1739_ = lean_ctor_get(v___x_1732_, 7);
                    v_snapshotTasks_1740_ = lean_ctor_get(v___x_1732_, 8);
                    v_isSharedCheck_1749_ = (!lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1749_ == 0 {
                        v_unused_1750_ = lean_ctor_get(v___x_1732_, 5);
                        lean_dec(v_unused_1750_);
                        v___x_1742_ = v___x_1732_;
                        v_isShared_1743_ = v_isSharedCheck_1749_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1740_);
                        lean_inc(v_infoState_1739_);
                        lean_inc(v_messages_1738_);
                        lean_inc(v_traceState_1737_);
                        lean_inc(v_auxDeclNGen_1736_);
                        lean_inc(v_ngen_1735_);
                        lean_inc(v_nextMacroScope_1734_);
                        lean_inc(v_env_1733_);
                        lean_dec(v___x_1732_);
                        v___x_1742_ = lean_box(0);
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
                    lean_ctor_set(v___x_1742_, 5, v___x_1656_);
                    lean_ctor_set(v___x_1742_, 0, v___x_1744_);
                    v___x_1746_ = v___x_1742_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1744_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_nextMacroScope_1734_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_ngen_1735_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_auxDeclNGen_1736_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 4, v_traceState_1737_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 5, v___x_1656_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 6, v_messages_1738_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 7, v_infoState_1739_);
                    lean_ctor_set(v_reuseFailAlloc_1748_, 8, v_snapshotTasks_1740_);
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
                v_fileName_1761_ = lean_ctor_get(v___y_1758_, 0);
                v_fileMap_1762_ = lean_ctor_get(v___y_1758_, 1);
                v_currRecDepth_1763_ = lean_ctor_get(v___y_1758_, 3);
                v_ref_1764_ = lean_ctor_get(v___y_1758_, 5);
                v_currNamespace_1765_ = lean_ctor_get(v___y_1758_, 6);
                v_openDecls_1766_ = lean_ctor_get(v___y_1758_, 7);
                v_initHeartbeats_1767_ = lean_ctor_get(v___y_1758_, 8);
                v_maxHeartbeats_1768_ = lean_ctor_get(v___y_1758_, 9);
                v_quotContext_1769_ = lean_ctor_get(v___y_1758_, 10);
                v_currMacroScope_1770_ = lean_ctor_get(v___y_1758_, 11);
                v_cancelTk_x3f_1771_ = lean_ctor_get(v___y_1758_, 12);
                v_suppressElabErrors_1772_ = lean_ctor_get_uint8(
                    v___y_1758_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1773_ = lean_ctor_get(v___y_1758_, 13);
                v_isSharedCheck_1786_ = (!lean_is_exclusive(v___y_1758_)) as u8;
                if v_isSharedCheck_1786_ == 0 {
                    v_unused_1787_ = lean_ctor_get(v___y_1758_, 4);
                    lean_dec(v_unused_1787_);
                    v_unused_1788_ = lean_ctor_get(v___y_1758_, 2);
                    lean_dec(v_unused_1788_);
                    v___x_1775_ = v___y_1758_;
                    v_isShared_1776_ = v_isSharedCheck_1786_;
                    state = 18;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_1773_);
                    lean_inc(v_cancelTk_x3f_1771_);
                    lean_inc(v_currMacroScope_1770_);
                    lean_inc(v_quotContext_1769_);
                    lean_inc(v_maxHeartbeats_1768_);
                    lean_inc(v_initHeartbeats_1767_);
                    lean_inc(v_openDecls_1766_);
                    lean_inc(v_currNamespace_1765_);
                    lean_inc(v_ref_1764_);
                    lean_inc(v_currRecDepth_1763_);
                    lean_inc(v_fileMap_1762_);
                    lean_inc(v_fileName_1761_);
                    lean_dec(v___y_1758_);
                    v___x_1775_ = lean_box(0);
                    v_isShared_1776_ = v_isSharedCheck_1786_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_env_1777_ = lean_ctor_get(v___x_1760_, 0);
                lean_inc_ref(v_env_1777_);
                lean_dec(v___x_1760_);
                v___x_1778_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
                    v___y_1756_,
                    v___y_1757_,
                );
                lean_inc_ref(v_inheritedTraceOptions_1773_);
                lean_inc(v_cancelTk_x3f_1771_);
                lean_inc(v_currMacroScope_1770_);
                lean_inc(v_quotContext_1769_);
                lean_inc(v_maxHeartbeats_1768_);
                lean_inc(v_initHeartbeats_1767_);
                lean_inc(v_openDecls_1766_);
                lean_inc(v_currNamespace_1765_);
                lean_inc(v_ref_1764_);
                lean_inc(v_currRecDepth_1763_);
                lean_inc_ref(v___y_1756_);
                lean_inc_ref(v_fileMap_1762_);
                lean_inc_ref(v_fileName_1761_);
                if v_isShared_1776_ == 0 {
                    lean_ctor_set(v___x_1775_, 4, v___x_1778_);
                    lean_ctor_set(v___x_1775_, 2, v___y_1756_);
                    v___x_1780_ = v___x_1775_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fileName_1761_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_fileMap_1762_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 2, v___y_1756_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_currRecDepth_1763_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 4, v___x_1778_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_ref_1764_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 6, v_currNamespace_1765_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 7, v_openDecls_1766_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 8, v_initHeartbeats_1767_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 9, v_maxHeartbeats_1768_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 10, v_quotContext_1769_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 11, v_currMacroScope_1770_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 12, v_cancelTk_x3f_1771_);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 13, v_inheritedTraceOptions_1773_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1785_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1772_,
                    );
                    v___x_1780_ = v_reuseFailAlloc_1785_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                lean_ctor_set_uint8(
                    v___x_1780_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
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
                lean_dec_ref(v_env_1777_);
                if v___x_1784_ == 0 {
                    if v___x_1783_ == 0 {
                        lean_dec_ref(v___x_1780_);
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
                        lean_dec_ref(v_inheritedTraceOptions_1773_);
                        lean_dec(v_cancelTk_x3f_1771_);
                        lean_dec(v_currMacroScope_1770_);
                        lean_dec(v_quotContext_1769_);
                        lean_dec(v_maxHeartbeats_1768_);
                        lean_dec(v_initHeartbeats_1767_);
                        lean_dec(v_openDecls_1766_);
                        lean_dec(v_currNamespace_1765_);
                        lean_dec(v_ref_1764_);
                        lean_dec(v_currRecDepth_1763_);
                        lean_dec_ref(v_fileMap_1762_);
                        lean_dec_ref(v_fileName_1761_);
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
                    lean_dec_ref(v_inheritedTraceOptions_1773_);
                    lean_dec(v_cancelTk_x3f_1771_);
                    lean_dec(v_currMacroScope_1770_);
                    lean_dec(v_quotContext_1769_);
                    lean_dec(v_maxHeartbeats_1768_);
                    lean_dec(v_initHeartbeats_1767_);
                    lean_dec(v_openDecls_1766_);
                    lean_dec(v_currNamespace_1765_);
                    lean_dec(v_ref_1764_);
                    lean_dec(v_currRecDepth_1763_);
                    lean_dec_ref(v_fileMap_1762_);
                    lean_dec_ref(v_fileName_1761_);
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
                    v_env_1797_ = lean_ctor_get(v___x_1796_, 0);
                    v_nextMacroScope_1798_ = lean_ctor_get(v___x_1796_, 1);
                    v_ngen_1799_ = lean_ctor_get(v___x_1796_, 2);
                    v_auxDeclNGen_1800_ = lean_ctor_get(v___x_1796_, 3);
                    v_traceState_1801_ = lean_ctor_get(v___x_1796_, 4);
                    v_messages_1802_ = lean_ctor_get(v___x_1796_, 6);
                    v_infoState_1803_ = lean_ctor_get(v___x_1796_, 7);
                    v_snapshotTasks_1804_ = lean_ctor_get(v___x_1796_, 8);
                    v_isSharedCheck_1813_ = (!lean_is_exclusive(v___x_1796_)) as u8;
                    if v_isSharedCheck_1813_ == 0 {
                        v_unused_1814_ = lean_ctor_get(v___x_1796_, 5);
                        lean_dec(v_unused_1814_);
                        v___x_1806_ = v___x_1796_;
                        v_isShared_1807_ = v_isSharedCheck_1813_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1804_);
                        lean_inc(v_infoState_1803_);
                        lean_inc(v_messages_1802_);
                        lean_inc(v_traceState_1801_);
                        lean_inc(v_auxDeclNGen_1800_);
                        lean_inc(v_ngen_1799_);
                        lean_inc(v_nextMacroScope_1798_);
                        lean_inc(v_env_1797_);
                        lean_dec(v___x_1796_);
                        v___x_1806_ = lean_box(0);
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
                    lean_ctor_set(v___x_1806_, 5, v___x_1656_);
                    lean_ctor_set(v___x_1806_, 0, v___x_1808_);
                    v___x_1810_ = v___x_1806_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_nextMacroScope_1798_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_ngen_1799_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_auxDeclNGen_1800_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_traceState_1801_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 5, v___x_1656_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 6, v_messages_1802_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 7, v_infoState_1803_);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 8, v_snapshotTasks_1804_);
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
                v_fileName_1820_ = lean_ctor_get(v___y_1817_, 0);
                v_fileMap_1821_ = lean_ctor_get(v___y_1817_, 1);
                v_currRecDepth_1822_ = lean_ctor_get(v___y_1817_, 3);
                v_ref_1823_ = lean_ctor_get(v___y_1817_, 5);
                v_currNamespace_1824_ = lean_ctor_get(v___y_1817_, 6);
                v_openDecls_1825_ = lean_ctor_get(v___y_1817_, 7);
                v_initHeartbeats_1826_ = lean_ctor_get(v___y_1817_, 8);
                v_maxHeartbeats_1827_ = lean_ctor_get(v___y_1817_, 9);
                v_quotContext_1828_ = lean_ctor_get(v___y_1817_, 10);
                v_currMacroScope_1829_ = lean_ctor_get(v___y_1817_, 11);
                v_cancelTk_x3f_1830_ = lean_ctor_get(v___y_1817_, 12);
                v_suppressElabErrors_1831_ = lean_ctor_get_uint8(
                    v___y_1817_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1832_ = lean_ctor_get(v___y_1817_, 13);
                v_isSharedCheck_1846_ = (!lean_is_exclusive(v___y_1817_)) as u8;
                if v_isSharedCheck_1846_ == 0 {
                    v_unused_1847_ = lean_ctor_get(v___y_1817_, 4);
                    lean_dec(v_unused_1847_);
                    v_unused_1848_ = lean_ctor_get(v___y_1817_, 2);
                    lean_dec(v_unused_1848_);
                    v___x_1834_ = v___y_1817_;
                    v_isShared_1835_ = v_isSharedCheck_1846_;
                    state = 24;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_1832_);
                    lean_inc(v_cancelTk_x3f_1830_);
                    lean_inc(v_currMacroScope_1829_);
                    lean_inc(v_quotContext_1828_);
                    lean_inc(v_maxHeartbeats_1827_);
                    lean_inc(v_initHeartbeats_1826_);
                    lean_inc(v_openDecls_1825_);
                    lean_inc(v_currNamespace_1824_);
                    lean_inc(v_ref_1823_);
                    lean_inc(v_currRecDepth_1822_);
                    lean_inc(v_fileMap_1821_);
                    lean_inc(v_fileName_1820_);
                    lean_dec(v___y_1817_);
                    v___x_1834_ = lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1846_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_env_1836_ = lean_ctor_get(v___x_1819_, 0);
                lean_inc_ref(v_env_1836_);
                lean_dec(v___x_1819_);
                v___x_1837_ = l_Lean_maxRecDepth;
                v___x_1838_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(
                    v___x_1752_,
                    v___x_1837_,
                );
                lean_inc_ref(v___x_1752_);
                if v_isShared_1835_ == 0 {
                    lean_ctor_set(v___x_1834_, 4, v___x_1838_);
                    lean_ctor_set(v___x_1834_, 2, v___x_1752_);
                    v___x_1840_ = v___x_1834_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fileName_1820_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_fileMap_1821_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 2, v___x_1752_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_currRecDepth_1822_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 4, v___x_1838_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_ref_1823_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_currNamespace_1824_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_openDecls_1825_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 8, v_initHeartbeats_1826_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_maxHeartbeats_1827_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 10, v_quotContext_1828_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 11, v_currMacroScope_1829_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 12, v_cancelTk_x3f_1830_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 13, v_inheritedTraceOptions_1832_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1845_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1831_,
                    );
                    v___x_1840_ = v_reuseFailAlloc_1845_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                lean_ctor_set_uint8(
                    v___x_1840_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
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
                lean_dec_ref(v_env_1836_);
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
                    v_env_1852_ = lean_ctor_get(v___x_1851_, 0);
                    v_nextMacroScope_1853_ = lean_ctor_get(v___x_1851_, 1);
                    v_ngen_1854_ = lean_ctor_get(v___x_1851_, 2);
                    v_auxDeclNGen_1855_ = lean_ctor_get(v___x_1851_, 3);
                    v_traceState_1856_ = lean_ctor_get(v___x_1851_, 4);
                    v_messages_1857_ = lean_ctor_get(v___x_1851_, 6);
                    v_infoState_1858_ = lean_ctor_get(v___x_1851_, 7);
                    v_snapshotTasks_1859_ = lean_ctor_get(v___x_1851_, 8);
                    v_isSharedCheck_1868_ = (!lean_is_exclusive(v___x_1851_)) as u8;
                    if v_isSharedCheck_1868_ == 0 {
                        v_unused_1869_ = lean_ctor_get(v___x_1851_, 5);
                        lean_dec(v_unused_1869_);
                        v___x_1861_ = v___x_1851_;
                        v_isShared_1862_ = v_isSharedCheck_1868_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1859_);
                        lean_inc(v_infoState_1858_);
                        lean_inc(v_messages_1857_);
                        lean_inc(v_traceState_1856_);
                        lean_inc(v_auxDeclNGen_1855_);
                        lean_inc(v_ngen_1854_);
                        lean_inc(v_nextMacroScope_1853_);
                        lean_inc(v_env_1852_);
                        lean_dec(v___x_1851_);
                        v___x_1861_ = lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1868_;
                        state = 27;
                        continue;
                    }
                } else {
                    lean_inc_ref(v___y_1594_);
                    v___y_1817_ = v___y_1594_;
                    v___y_1818_ = v___y_1595_;
                    state = 23;
                    continue;
                }
            }
            27 => {
                v___x_1863_ = l_Lean_Kernel_enableDiag(v_env_1852_, v___x_1815_);
                if v_isShared_1862_ == 0 {
                    lean_ctor_set(v___x_1861_, 5, v___x_1656_);
                    lean_ctor_set(v___x_1861_, 0, v___x_1863_);
                    v___x_1865_ = v___x_1861_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_nextMacroScope_1853_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_ngen_1854_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_auxDeclNGen_1855_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_traceState_1856_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 5, v___x_1656_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_messages_1857_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 7, v_infoState_1858_);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_snapshotTasks_1859_);
                    v___x_1865_ = v_reuseFailAlloc_1867_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_1866_ = lean_st_ref_set(v___y_1595_, v___x_1865_);
                lean_inc_ref(v___y_1594_);
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
    mut v___x_1879_: *mut LeanObject,
    mut v___x_1880_: *mut LeanObject,
    mut v___x_1881_: *mut LeanObject,
    mut v_tacticName_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1889_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1887_);
    lean_dec(v___y_1885_);
    lean_dec_ref(v___y_1884_);
    return v_res_1889_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(
    mut v_stx_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v_fileMap_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1893_ = 0;
                v___x_1894_ = l_Lean_Syntax_getRange_x3f(v_stx_1890_, v___x_1893_);
                if lean_obj_tag(v___x_1894_) == 1 {
                    v_val_1895_ = lean_ctor_get(v___x_1894_, 0);
                    v_isSharedCheck_1907_ = (!lean_is_exclusive(v___x_1894_)) as u8;
                    if v_isSharedCheck_1907_ == 0 {
                        v___x_1897_ = v___x_1894_;
                        v_isShared_1898_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1895_);
                        lean_dec(v___x_1894_);
                        v___x_1897_ = lean_box(0);
                        v_isShared_1898_ = v_isSharedCheck_1907_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1894_);
                    v___x_1908_ = lean_box(0);
                    v___x_1909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1909_, 0, v___x_1908_);
                    return v___x_1909_;
                }
            }
            1 => {
                v_fileMap_1899_ = lean_ctor_get(v___y_1891_, 1);
                v_start_1900_ = lean_ctor_get(v_val_1895_, 0);
                lean_inc(v_start_1900_);
                v_stop_1901_ = lean_ctor_get(v_val_1895_, 1);
                lean_inc(v_stop_1901_);
                lean_dec(v_val_1895_);
                lean_inc_ref(v_fileMap_1899_);
                v___x_1902_ = l_Lean_DeclarationRange_ofStringPositions(
                    v_fileMap_1899_,
                    v_start_1900_,
                    v_stop_1901_,
                );
                lean_dec(v_stop_1901_);
                lean_dec(v_start_1900_);
                if v_isShared_1898_ == 0 {
                    lean_ctor_set(v___x_1897_, 0, v___x_1902_);
                    v___x_1904_ = v___x_1897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1902_);
                    v___x_1904_ = v_reuseFailAlloc_1906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1905_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                return v___x_1905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(
    mut v_stx_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1913_: *mut LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_1910_, v___y_1911_);
    lean_dec_ref(v___y_1911_);
    lean_dec(v_stx_1910_);
    return v_res_1913_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(
    mut v_declName_1914_: *mut LeanObject,
    mut v_declRanges_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1945_: u8 = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut v_unused_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut v_unused_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1919_ = l_Lean_Name_isAnonymous(v_declName_1914_);
                if v___x_1919_ == 0 {
                    v___x_1920_ = lean_st_ref_take(v___y_1917_);
                    v_env_1921_ = lean_ctor_get(v___x_1920_, 0);
                    v_nextMacroScope_1922_ = lean_ctor_get(v___x_1920_, 1);
                    v_ngen_1923_ = lean_ctor_get(v___x_1920_, 2);
                    v_auxDeclNGen_1924_ = lean_ctor_get(v___x_1920_, 3);
                    v_traceState_1925_ = lean_ctor_get(v___x_1920_, 4);
                    v_messages_1926_ = lean_ctor_get(v___x_1920_, 6);
                    v_infoState_1927_ = lean_ctor_get(v___x_1920_, 7);
                    v_snapshotTasks_1928_ = lean_ctor_get(v___x_1920_, 8);
                    v_isSharedCheck_1956_ = (!lean_is_exclusive(v___x_1920_)) as u8;
                    if v_isSharedCheck_1956_ == 0 {
                        v_unused_1957_ = lean_ctor_get(v___x_1920_, 5);
                        lean_dec(v_unused_1957_);
                        v___x_1930_ = v___x_1920_;
                        v_isShared_1931_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_1928_);
                        lean_inc(v_infoState_1927_);
                        lean_inc(v_messages_1926_);
                        lean_inc(v_traceState_1925_);
                        lean_inc(v_auxDeclNGen_1924_);
                        lean_inc(v_ngen_1923_);
                        lean_inc(v_nextMacroScope_1922_);
                        lean_inc(v_env_1921_);
                        lean_dec(v___x_1920_);
                        v___x_1930_ = lean_box(0);
                        v_isShared_1931_ = v_isSharedCheck_1956_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_declRanges_1915_);
                    lean_dec(v_declName_1914_);
                    v___x_1958_ = lean_box(0);
                    v___x_1959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1959_, 0, v___x_1958_);
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
                v___x_1934_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_1931_ == 0 {
                    lean_ctor_set(v___x_1930_, 5, v___x_1934_);
                    lean_ctor_set(v___x_1930_, 0, v___x_1933_);
                    v___x_1936_ = v___x_1930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1933_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_nextMacroScope_1922_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_ngen_1923_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_auxDeclNGen_1924_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_traceState_1925_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 5, v___x_1934_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_messages_1926_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 7, v_infoState_1927_);
                    lean_ctor_set(v_reuseFailAlloc_1955_, 8, v_snapshotTasks_1928_);
                    v___x_1936_ = v_reuseFailAlloc_1955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1937_ = lean_st_ref_set(v___y_1917_, v___x_1936_);
                v___x_1938_ = lean_st_ref_take(v___y_1916_);
                v_mctx_1939_ = lean_ctor_get(v___x_1938_, 0);
                v_zetaDeltaFVarIds_1940_ = lean_ctor_get(v___x_1938_, 2);
                v_postponed_1941_ = lean_ctor_get(v___x_1938_, 3);
                v_diag_1942_ = lean_ctor_get(v___x_1938_, 4);
                v_isSharedCheck_1953_ = (!lean_is_exclusive(v___x_1938_)) as u8;
                if v_isSharedCheck_1953_ == 0 {
                    v_unused_1954_ = lean_ctor_get(v___x_1938_, 1);
                    lean_dec(v_unused_1954_);
                    v___x_1944_ = v___x_1938_;
                    v_isShared_1945_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1942_);
                    lean_inc(v_postponed_1941_);
                    lean_inc(v_zetaDeltaFVarIds_1940_);
                    lean_inc(v_mctx_1939_);
                    lean_dec(v___x_1938_);
                    v___x_1944_ = lean_box(0);
                    v_isShared_1945_ = v_isSharedCheck_1953_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1946_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_1945_ == 0 {
                    lean_ctor_set(v___x_1944_, 1, v___x_1946_);
                    v___x_1948_ = v___x_1944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_mctx_1939_);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1946_);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_zetaDeltaFVarIds_1940_);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_postponed_1941_);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_diag_1942_);
                    v___x_1948_ = v_reuseFailAlloc_1952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1949_ = lean_st_ref_set(v___y_1916_, v___x_1948_);
                v___x_1950_ = lean_box(0);
                v___x_1951_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1951_, 0, v___x_1950_);
                return v___x_1951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(
    mut v_declName_1960_: *mut LeanObject,
    mut v_declRanges_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1965_: *mut LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1960_, v_declRanges_1961_, v___y_1962_, v___y_1963_);
    lean_dec(v___y_1963_);
    lean_dec(v___y_1962_);
    return v_res_1965_;
}
pub unsafe fn l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(
    mut v_declName_1966_: *mut LeanObject,
    mut v_rangeStx_1967_: *mut LeanObject,
    mut v_selectionRangeStx_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
    mut v___y_1970_: *mut LeanObject,
    mut v___y_1971_: *mut LeanObject,
    mut v___y_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_val_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1974_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_rangeStx_1967_, v___y_1971_);
                v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
                v_isSharedCheck_1991_ = (!lean_is_exclusive(v___x_1974_)) as u8;
                if v_isSharedCheck_1991_ == 0 {
                    v___x_1977_ = v___x_1974_;
                    v_isShared_1978_ = v_isSharedCheck_1991_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1975_);
                    lean_dec(v___x_1974_);
                    v___x_1977_ = lean_box(0);
                    v_isShared_1978_ = v_isSharedCheck_1991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1975_) == 1 {
                    lean_del_object(v___x_1977_);
                    v_val_1979_ = lean_ctor_get(v_a_1975_, 0);
                    lean_inc(v_val_1979_);
                    lean_dec_ref_known(v_a_1975_, 1);
                    v___x_1980_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_selectionRangeStx_1968_, v___y_1971_);
                    v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
                    lean_inc(v_a_1981_);
                    lean_dec_ref(v___x_1980_);
                    if lean_obj_tag(v_a_1981_) == 0 {
                        lean_inc(v_val_1979_);
                        v_a_1983_ = v_val_1979_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1986_ = lean_ctor_get(v_a_1981_, 0);
                        lean_inc(v_val_1986_);
                        lean_dec_ref_known(v_a_1981_, 1);
                        v_a_1983_ = v_val_1986_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1975_);
                    lean_dec(v_declName_1966_);
                    v___x_1987_ = lean_box(0);
                    if v_isShared_1978_ == 0 {
                        lean_ctor_set(v___x_1977_, 0, v___x_1987_);
                        v___x_1989_ = v___x_1977_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
                        v___x_1989_ = v_reuseFailAlloc_1990_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1984_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1984_, 0, v_val_1979_);
                lean_ctor_set(v___x_1984_, 1, v_a_1983_);
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
    mut v_declName_1992_: *mut LeanObject,
    mut v_rangeStx_1993_: *mut LeanObject,
    mut v_selectionRangeStx_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2000_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1998_);
    lean_dec_ref(v___y_1997_);
    lean_dec(v___y_1996_);
    lean_dec_ref(v___y_1995_);
    lean_dec(v_selectionRangeStx_1994_);
    lean_dec(v_rangeStx_1993_);
    return v_res_2000_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(
    mut v_a_2001_: *mut LeanObject,
    mut v_a_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2001_) == 0 {
                    v___x_2003_ = l_List_reverse___redArg(v_a_2002_);
                    return v___x_2003_;
                } else {
                    v_head_2004_ = lean_ctor_get(v_a_2001_, 0);
                    v_tail_2005_ = lean_ctor_get(v_a_2001_, 1);
                    v_isSharedCheck_2014_ = (!lean_is_exclusive(v_a_2001_)) as u8;
                    if v_isSharedCheck_2014_ == 0 {
                        v___x_2007_ = v_a_2001_;
                        v_isShared_2008_ = v_isSharedCheck_2014_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2005_);
                        lean_inc(v_head_2004_);
                        lean_dec(v_a_2001_);
                        v___x_2007_ = lean_box(0);
                        v_isShared_2008_ = v_isSharedCheck_2014_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2009_ = l_Lean_mkLevelParam(v_head_2004_);
                if v_isShared_2008_ == 0 {
                    lean_ctor_set(v___x_2007_, 1, v_a_2002_);
                    lean_ctor_set(v___x_2007_, 0, v___x_2009_);
                    v___x_2011_ = v___x_2007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2009_);
                    lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_a_2002_);
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
    mut v_env_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_unused_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_unused_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2019_ = lean_st_ref_take(v___y_2017_);
                v_nextMacroScope_2020_ = lean_ctor_get(v___x_2019_, 1);
                v_ngen_2021_ = lean_ctor_get(v___x_2019_, 2);
                v_auxDeclNGen_2022_ = lean_ctor_get(v___x_2019_, 3);
                v_traceState_2023_ = lean_ctor_get(v___x_2019_, 4);
                v_messages_2024_ = lean_ctor_get(v___x_2019_, 6);
                v_infoState_2025_ = lean_ctor_get(v___x_2019_, 7);
                v_snapshotTasks_2026_ = lean_ctor_get(v___x_2019_, 8);
                v_isSharedCheck_2052_ = (!lean_is_exclusive(v___x_2019_)) as u8;
                if v_isSharedCheck_2052_ == 0 {
                    v_unused_2053_ = lean_ctor_get(v___x_2019_, 5);
                    lean_dec(v_unused_2053_);
                    v_unused_2054_ = lean_ctor_get(v___x_2019_, 0);
                    lean_dec(v_unused_2054_);
                    v___x_2028_ = v___x_2019_;
                    v_isShared_2029_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2026_);
                    lean_inc(v_infoState_2025_);
                    lean_inc(v_messages_2024_);
                    lean_inc(v_traceState_2023_);
                    lean_inc(v_auxDeclNGen_2022_);
                    lean_inc(v_ngen_2021_);
                    lean_inc(v_nextMacroScope_2020_);
                    lean_dec(v___x_2019_);
                    v___x_2028_ = lean_box(0);
                    v_isShared_2029_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2030_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11,
                );
                if v_isShared_2029_ == 0 {
                    lean_ctor_set(v___x_2028_, 5, v___x_2030_);
                    lean_ctor_set(v___x_2028_, 0, v_env_2015_);
                    v___x_2032_ = v___x_2028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_env_2015_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_nextMacroScope_2020_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_ngen_2021_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_auxDeclNGen_2022_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_traceState_2023_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 5, v___x_2030_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 6, v_messages_2024_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 7, v_infoState_2025_);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 8, v_snapshotTasks_2026_);
                    v___x_2032_ = v_reuseFailAlloc_2051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2033_ = lean_st_ref_set(v___y_2017_, v___x_2032_);
                v___x_2034_ = lean_st_ref_take(v___y_2016_);
                v_mctx_2035_ = lean_ctor_get(v___x_2034_, 0);
                v_zetaDeltaFVarIds_2036_ = lean_ctor_get(v___x_2034_, 2);
                v_postponed_2037_ = lean_ctor_get(v___x_2034_, 3);
                v_diag_2038_ = lean_ctor_get(v___x_2034_, 4);
                v_isSharedCheck_2049_ = (!lean_is_exclusive(v___x_2034_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v_unused_2050_ = lean_ctor_get(v___x_2034_, 1);
                    lean_dec(v_unused_2050_);
                    v___x_2040_ = v___x_2034_;
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_2038_);
                    lean_inc(v_postponed_2037_);
                    lean_inc(v_zetaDeltaFVarIds_2036_);
                    lean_inc(v_mctx_2035_);
                    lean_dec(v___x_2034_);
                    v___x_2040_ = lean_box(0);
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2042_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once),
                    _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12,
                );
                if v_isShared_2041_ == 0 {
                    lean_ctor_set(v___x_2040_, 1, v___x_2042_);
                    v___x_2044_ = v___x_2040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_mctx_2035_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_zetaDeltaFVarIds_2036_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_postponed_2037_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_diag_2038_);
                    v___x_2044_ = v_reuseFailAlloc_2048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2045_ = lean_st_ref_set(v___y_2016_, v___x_2044_);
                v___x_2046_ = lean_box(0);
                v___x_2047_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                return v___x_2047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(
    mut v_env_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2059_: *mut LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2055_, v___y_2056_, v___y_2057_);
    lean_dec(v___y_2057_);
    lean_dec(v___y_2056_);
    return v_res_2059_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
    mut v_env_2060_: *mut LeanObject,
    mut v_x_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2074_: u8 = 0;
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v_unused_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_unused_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2067_ = lean_st_ref_get(v___y_2065_);
                v_env_2068_ = lean_ctor_get(v___x_2067_, 0);
                lean_inc_ref(v_env_2068_);
                lean_dec(v___x_2067_);
                v___x_2080_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2060_, v___y_2063_, v___y_2065_);
                lean_dec_ref(v___x_2080_);
                lean_inc(v___y_2065_);
                lean_inc_ref(v___y_2064_);
                lean_inc(v___y_2063_);
                lean_inc_ref(v___y_2062_);
                v___x_2081_ = lean_apply_5(
                    v_x_2061_,
                    v___y_2062_,
                    v___y_2063_,
                    v___y_2064_,
                    v___y_2065_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2081_) == 0 {
                    v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
                    lean_inc(v_a_2082_);
                    lean_dec_ref_known(v___x_2081_, 1);
                    v___x_2083_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2068_, v___y_2063_, v___y_2065_);
                    v_isSharedCheck_2090_ = (!lean_is_exclusive(v___x_2083_)) as u8;
                    if v_isSharedCheck_2090_ == 0 {
                        v_unused_2091_ = lean_ctor_get(v___x_2083_, 0);
                        lean_dec(v_unused_2091_);
                        v___x_2085_ = v___x_2083_;
                        v_isShared_2086_ = v_isSharedCheck_2090_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_2083_);
                        v___x_2085_ = lean_box(0);
                        v_isShared_2086_ = v_isSharedCheck_2090_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2092_ = lean_ctor_get(v___x_2081_, 0);
                    lean_inc(v_a_2092_);
                    lean_dec_ref_known(v___x_2081_, 1);
                    v_a_2070_ = v_a_2092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2071_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2068_, v___y_2063_, v___y_2065_);
                v_isSharedCheck_2078_ = (!lean_is_exclusive(v___x_2071_)) as u8;
                if v_isSharedCheck_2078_ == 0 {
                    v_unused_2079_ = lean_ctor_get(v___x_2071_, 0);
                    lean_dec(v_unused_2079_);
                    v___x_2073_ = v___x_2071_;
                    v_isShared_2074_ = v_isSharedCheck_2078_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_2071_);
                    v___x_2073_ = lean_box(0);
                    v_isShared_2074_ = v_isSharedCheck_2078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2074_ == 0 {
                    lean_ctor_set_tag(v___x_2073_, 1);
                    lean_ctor_set(v___x_2073_, 0, v_a_2070_);
                    v___x_2076_ = v___x_2073_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2070_);
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
                    lean_ctor_set(v___x_2085_, 0, v_a_2082_);
                    v___x_2088_ = v___x_2085_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2082_);
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
    mut v_env_2093_: *mut LeanObject,
    mut v_x_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2100_: *mut LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
        v_env_2093_,
        v_x_2094_,
        v___y_2095_,
        v___y_2096_,
        v___y_2097_,
        v___y_2098_,
    );
    lean_dec(v___y_2098_);
    lean_dec_ref(v___y_2097_);
    lean_dec(v___y_2096_);
    lean_dec_ref(v___y_2095_);
    return v_res_2100_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__0() -> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = lean_box(0);
    v___x_2102_ = lean_unsigned_to_nat(16);
    v___x_2103_ = lean_mk_array(v___x_2102_, v___x_2101_);
    return v___x_2103_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__1() -> *mut LeanObject {
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v___x_2104_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__0_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__0,
    );
    v___x_2105_ = lean_unsigned_to_nat(0);
    v___x_2106_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2106_, 0, v___x_2105_);
    lean_ctor_set(v___x_2106_, 1, v___x_2104_);
    return v___x_2106_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__3() -> *mut LeanObject {
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_Meta_nativeEqTrue___closed__2;
    v___x_2110_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__1_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__1,
    );
    v___x_2111_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2111_, 0, v___x_2110_);
    lean_ctor_set(v___x_2111_, 1, v___x_2110_);
    lean_ctor_set(v___x_2111_, 2, v___x_2109_);
    return v___x_2111_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__12() -> *mut LeanObject {
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    v___x_2124_ = lean_unsigned_to_nat(1);
    v___x_2125_ = l_Lean_Level_ofNat(v___x_2124_);
    return v___x_2125_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__13() -> *mut LeanObject {
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    v___x_2126_ = lean_box(0);
    v___x_2127_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__12_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__12,
    );
    v___x_2128_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2128_, 0, v___x_2127_);
    lean_ctor_set(v___x_2128_, 1, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__14() -> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    v___x_2129_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__13_once),
        _init_l_Lean_Meta_nativeEqTrue___closed__13,
    );
    v___x_2130_ = l_Lean_Meta_nativeEqTrue___closed__11;
    v___x_2131_ = l_Lean_mkConst(v___x_2130_, v___x_2129_);
    return v___x_2131_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__15() -> *mut LeanObject {
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    v___x_2132_ = lean_box(0);
    v___x_2133_ = l_Lean_Meta_nativeEqTrue___lam__0___closed__7;
    v___x_2134_ = l_Lean_mkConst(v___x_2133_, v___x_2132_);
    return v___x_2134_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__18() -> *mut LeanObject {
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    v___x_2139_ = lean_box(0);
    v___x_2140_ = l_Lean_Meta_nativeEqTrue___closed__17;
    v___x_2141_ = l_Lean_mkConst(v___x_2140_, v___x_2139_);
    return v___x_2141_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__20() -> *mut LeanObject {
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_Meta_nativeEqTrue___closed__19;
    v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn _init_l_Lean_Meta_nativeEqTrue___closed__22() -> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    v___x_2146_ = l_Lean_Meta_nativeEqTrue___closed__21;
    v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn l_Lean_Meta_nativeEqTrue(
    mut v_tacticName_2148_: *mut LeanObject,
    mut v_e_2149_: *mut LeanObject,
    mut v_axiomDeclRange_x3f_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v_env_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v___x_2192_: u8 = 0;
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_a_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_reuseFailAlloc_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut v_unused_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2164_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(
                        v_e_2149_, v_a_2152_,
                    );
                v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
                lean_inc(v_a_2165_);
                lean_dec_ref(v___x_2164_);
                v___x_2271_ = l_Lean_Expr_hasFVar(v_a_2165_);
                if v___x_2271_ == 0 {
                    v___y_2250_ = v_a_2151_;
                    v___y_2251_ = v_a_2152_;
                    v___y_2252_ = v_a_2153_;
                    v___y_2253_ = v_a_2154_;
                    state = 15;
                    continue;
                } else {
                    v___x_2272_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_2273_ = l_Lean_MessageData_ofName(v_tacticName_2148_);
                    v___x_2274_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2274_, 0, v___x_2272_);
                    lean_ctor_set(v___x_2274_, 1, v___x_2273_);
                    v___x_2275_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__22),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__22_once),
                        _init_l_Lean_Meta_nativeEqTrue___closed__22,
                    );
                    v___x_2276_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2276_, 0, v___x_2274_);
                    lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                    v___x_2277_ = l_Lean_indentExpr(v_a_2165_);
                    v___x_2278_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2278_, 0, v___x_2276_);
                    lean_ctor_set(v___x_2278_, 1, v___x_2277_);
                    v___x_2279_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2278_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
                    v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
                    v_isSharedCheck_2287_ = (!lean_is_exclusive(v___x_2279_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2282_ = v___x_2279_;
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2280_);
                        lean_dec(v___x_2279_);
                        v___x_2282_ = lean_box(0);
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2159_ = lean_box(0);
                v___x_2160_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(
                    v___y_2158_,
                    v___x_2159_,
                );
                v___x_2161_ = l_Lean_mkConst(v___y_2157_, v___x_2160_);
                v___x_2162_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2162_, 0, v___x_2161_);
                v___x_2163_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2163_, 0, v___x_2162_);
                return v___x_2163_;
            }
            2 => {
                v___x_2171_ = lean_st_ref_get(v___y_2170_);
                v___x_2172_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__3_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__3,
                );
                lean_inc(v_a_2165_);
                v___x_2173_ = l_Lean_collectLevelParams(v___x_2172_, v_a_2165_);
                v_params_2174_ = lean_ctor_get(v___x_2173_, 2);
                v_isSharedCheck_2246_ = (!lean_is_exclusive(v___x_2173_)) as u8;
                if v_isSharedCheck_2246_ == 0 {
                    v_unused_2247_ = lean_ctor_get(v___x_2173_, 1);
                    lean_dec(v_unused_2247_);
                    v_unused_2248_ = lean_ctor_get(v___x_2173_, 0);
                    lean_dec(v_unused_2248_);
                    v___x_2176_ = v___x_2173_;
                    v_isShared_2177_ = v_isSharedCheck_2246_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_params_2174_);
                    lean_dec(v___x_2173_);
                    v___x_2176_ = lean_box(0);
                    v_isShared_2177_ = v_isSharedCheck_2246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_env_2178_ = lean_ctor_get(v___x_2171_, 0);
                lean_inc_ref(v_env_2178_);
                lean_dec(v___x_2171_);
                v___x_2179_ = lean_box(0);
                v___x_2180_ = lean_array_to_list(v_params_2174_);
                v___x_2181_ = l_Lean_Meta_nativeEqTrue___closed__5;
                lean_inc(v_tacticName_2148_);
                v___x_2182_ = l_Lean_Name_append(v___x_2181_, v_tacticName_2148_);
                v___x_2183_ = l_Lean_Meta_nativeEqTrue___closed__7;
                lean_inc(v___x_2182_);
                v___x_2184_ = l_Lean_Name_append(v___x_2182_, v___x_2183_);
                lean_inc(v_a_2165_);
                lean_inc(v___x_2180_);
                v___f_2185_ = lean_alloc_closure(
                    l_Lean_Meta_nativeEqTrue___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    5,
                );
                lean_closure_set(v___f_2185_, 0, v___x_2184_);
                lean_closure_set(v___f_2185_, 1, v___x_2180_);
                lean_closure_set(v___f_2185_, 2, v___x_2179_);
                lean_closure_set(v___f_2185_, 3, v_tacticName_2148_);
                lean_closure_set(v___f_2185_, 4, v_a_2165_);
                v___x_2186_ = l_Lean_Environment_unlockAsync(v_env_2178_);
                v___x_2187_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(
                    v___x_2186_,
                    v___f_2185_,
                    v___y_2167_,
                    v___y_2168_,
                    v___y_2169_,
                    v___y_2170_,
                );
                if lean_obj_tag(v___x_2187_) == 0 {
                    v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
                    v_isSharedCheck_2237_ = (!lean_is_exclusive(v___x_2187_)) as u8;
                    if v_isSharedCheck_2237_ == 0 {
                        v___x_2190_ = v___x_2187_;
                        v_isShared_2191_ = v_isSharedCheck_2237_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2188_);
                        lean_dec(v___x_2187_);
                        v___x_2190_ = lean_box(0);
                        v_isShared_2191_ = v_isSharedCheck_2237_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2182_);
                    lean_dec(v___x_2180_);
                    lean_del_object(v___x_2176_);
                    lean_dec(v_a_2165_);
                    v_a_2238_ = lean_ctor_get(v___x_2187_, 0);
                    v_isSharedCheck_2245_ = (!lean_is_exclusive(v___x_2187_)) as u8;
                    if v_isSharedCheck_2245_ == 0 {
                        v___x_2240_ = v___x_2187_;
                        v_isShared_2241_ = v_isSharedCheck_2245_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2238_);
                        lean_dec(v___x_2187_);
                        v___x_2240_ = lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2245_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2192_ = (lean_unbox(v_a_2188_) as u8);
                lean_dec(v_a_2188_);
                if v___x_2192_ == 0 {
                    lean_dec(v___x_2182_);
                    lean_dec(v___x_2180_);
                    lean_del_object(v___x_2176_);
                    lean_dec(v_a_2165_);
                    v___x_2193_ = lean_box(1);
                    if v_isShared_2191_ == 0 {
                        lean_ctor_set(v___x_2190_, 0, v___x_2193_);
                        v___x_2195_ = v___x_2190_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
                        v___x_2195_ = v_reuseFailAlloc_2196_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2190_);
                    v___x_2197_ = l_Lean_Meta_nativeEqTrue___closed__9;
                    v___x_2198_ = l_Lean_Name_append(v___x_2182_, v___x_2197_);
                    v___x_2199_ =
                        l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(
                            v___x_2198_,
                            v___y_2170_,
                        );
                    v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
                    v_isSharedCheck_2236_ = (!lean_is_exclusive(v___x_2199_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2202_ = v___x_2199_;
                        v_isShared_2203_ = v_isSharedCheck_2236_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2200_);
                        lean_dec(v___x_2199_);
                        v___x_2202_ = lean_box(0);
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
                v___x_2204_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__14_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__14,
                );
                v___x_2205_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__15_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__15,
                );
                v___x_2206_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__18_once),
                    _init_l_Lean_Meta_nativeEqTrue___closed__18,
                );
                v___x_2207_ = l_Lean_mkApp3(v___x_2204_, v___x_2205_, v_a_2165_, v___x_2206_);
                lean_inc(v___x_2180_);
                lean_inc(v_a_2200_);
                if v_isShared_2177_ == 0 {
                    lean_ctor_set(v___x_2176_, 2, v___x_2207_);
                    lean_ctor_set(v___x_2176_, 1, v___x_2180_);
                    lean_ctor_set(v___x_2176_, 0, v_a_2200_);
                    v___x_2209_ = v___x_2176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2200_);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2180_);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 2, v___x_2207_);
                    v___x_2209_ = v_reuseFailAlloc_2235_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2210_ = 0;
                v___x_2211_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2211_, 0, v___x_2209_);
                lean_ctor_set_uint8(
                    v___x_2211_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2210_,
                );
                if v_isShared_2203_ == 0 {
                    lean_ctor_set(v___x_2202_, 0, v___x_2211_);
                    v___x_2213_ = v___x_2202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2211_);
                    v___x_2213_ = v_reuseFailAlloc_2234_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2214_ = l_Lean_addDecl(v___x_2213_, v___x_2210_, v___y_2169_, v___y_2170_);
                if lean_obj_tag(v___x_2214_) == 0 {
                    lean_dec_ref_known(v___x_2214_, 1);
                    if lean_obj_tag(v_axiomDeclRange_x3f_2150_) == 1 {
                        v_val_2215_ = lean_ctor_get(v_axiomDeclRange_x3f_2150_, 0);
                        v___x_2216_ = lean_box(0);
                        lean_inc(v_a_2200_);
                        v___x_2217_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_a_2200_, v_val_2215_, v___x_2216_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
                        if lean_obj_tag(v___x_2217_) == 0 {
                            lean_dec_ref_known(v___x_2217_, 1);
                            v___y_2157_ = v_a_2200_;
                            v___y_2158_ = v___x_2180_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2200_);
                            lean_dec(v___x_2180_);
                            v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
                            v_isSharedCheck_2225_ = (!lean_is_exclusive(v___x_2217_)) as u8;
                            if v_isSharedCheck_2225_ == 0 {
                                v___x_2220_ = v___x_2217_;
                                v_isShared_2221_ = v_isSharedCheck_2225_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2218_);
                                lean_dec(v___x_2217_);
                                v___x_2220_ = lean_box(0);
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
                    lean_dec(v_a_2200_);
                    lean_dec(v___x_2180_);
                    v_a_2226_ = lean_ctor_get(v___x_2214_, 0);
                    v_isSharedCheck_2233_ = (!lean_is_exclusive(v___x_2214_)) as u8;
                    if v_isSharedCheck_2233_ == 0 {
                        v___x_2228_ = v___x_2214_;
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2226_);
                        lean_dec(v___x_2214_);
                        v___x_2228_ = lean_box(0);
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
                    v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
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
                    v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
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
                    v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
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
                    v___x_2255_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once),
                        _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1,
                    );
                    v___x_2256_ = l_Lean_MessageData_ofName(v_tacticName_2148_);
                    v___x_2257_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2257_, 0, v___x_2255_);
                    lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                    v___x_2258_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__20),
                        core::ptr::addr_of_mut!(l_Lean_Meta_nativeEqTrue___closed__20_once),
                        _init_l_Lean_Meta_nativeEqTrue___closed__20,
                    );
                    v___x_2259_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2259_, 0, v___x_2257_);
                    lean_ctor_set(v___x_2259_, 1, v___x_2258_);
                    v___x_2260_ = l_Lean_indentExpr(v_a_2165_);
                    v___x_2261_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2261_, 0, v___x_2259_);
                    lean_ctor_set(v___x_2261_, 1, v___x_2260_);
                    v___x_2262_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_2261_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
                    v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
                    v_isSharedCheck_2270_ = (!lean_is_exclusive(v___x_2262_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v___x_2265_ = v___x_2262_;
                        v_isShared_2266_ = v_isSharedCheck_2270_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2263_);
                        lean_dec(v___x_2262_);
                        v___x_2265_ = lean_box(0);
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
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
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
                    v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
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
    mut v_tacticName_2288_: *mut LeanObject,
    mut v_e_2289_: *mut LeanObject,
    mut v_axiomDeclRange_x3f_2290_: *mut LeanObject,
    mut v_a_2291_: *mut LeanObject,
    mut v_a_2292_: *mut LeanObject,
    mut v_a_2293_: *mut LeanObject,
    mut v_a_2294_: *mut LeanObject,
    mut v_a_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2296_: *mut LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Lean_Meta_nativeEqTrue(
        v_tacticName_2288_,
        v_e_2289_,
        v_axiomDeclRange_x3f_2290_,
        v_a_2291_,
        v_a_2292_,
        v_a_2293_,
        v_a_2294_,
    );
    lean_dec(v_a_2294_);
    lean_dec_ref(v_a_2293_);
    lean_dec(v_a_2292_);
    lean_dec_ref(v_a_2291_);
    lean_dec(v_axiomDeclRange_x3f_2290_);
    return v_res_2296_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(
    mut v_env_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2303_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_2297_, v___y_2299_, v___y_2301_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(
    mut v_env_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
    mut v___y_2309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2310_: *mut LeanObject = core::ptr::null_mut();
    v_res_2310_ =
        l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(
            v_env_2304_,
            v___y_2305_,
            v___y_2306_,
            v___y_2307_,
            v___y_2308_,
        );
    lean_dec(v___y_2308_);
    lean_dec_ref(v___y_2307_);
    lean_dec(v___y_2306_);
    lean_dec_ref(v___y_2305_);
    return v_res_2310_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(
    mut v_00_u03b1_2311_: *mut LeanObject,
    mut v_env_2312_: *mut LeanObject,
    mut v_x_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2320_: *mut LeanObject,
    mut v_env_2321_: *mut LeanObject,
    mut v_x_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(
        v_00_u03b1_2320_,
        v_env_2321_,
        v_x_2322_,
        v___y_2323_,
        v___y_2324_,
        v___y_2325_,
        v___y_2326_,
    );
    lean_dec(v___y_2326_);
    lean_dec_ref(v___y_2325_);
    lean_dec(v___y_2324_);
    lean_dec_ref(v___y_2323_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(
    mut v_stx_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_2329_, v___y_2332_);
    return v___x_2335_;
}
pub unsafe fn l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(
    mut v_stx_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2342_: *mut LeanObject = core::ptr::null_mut();
    v_res_2342_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(v_stx_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
    lean_dec(v___y_2340_);
    lean_dec_ref(v___y_2339_);
    lean_dec(v___y_2338_);
    lean_dec_ref(v___y_2337_);
    lean_dec(v_stx_2336_);
    return v_res_2342_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(
    mut v_declName_2343_: *mut LeanObject,
    mut v_declRanges_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    v___x_2350_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_2343_, v_declRanges_2344_, v___y_2346_, v___y_2348_);
    return v___x_2350_;
}
pub unsafe fn l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(
    mut v_declName_2351_: *mut LeanObject,
    mut v_declRanges_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2358_: *mut LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(v_declName_2351_, v_declRanges_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
    lean_dec(v___y_2356_);
    lean_dec_ref(v___y_2355_);
    lean_dec(v___y_2354_);
    lean_dec_ref(v___y_2353_);
    return v_res_2358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Native(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Native(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Native(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Native(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Native(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Native(builtin);
}
