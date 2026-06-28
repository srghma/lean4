// Lean compiler output
// Module: Lean.Elab.InfoTree.Main
// Imports: Init.Task Lean.Meta.PPGoal Lean.ReservedNameAction Init.Data.Format.Macro
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_nestD;
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_typeNameImpl;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_getTailInfo;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getHeadInfo, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_firstFrontendMacroScope, l_Lean_replaceRef,
    l_instInhabitedOfMonad___redArg, l_panic___redArg, lean_erase_macro_scopes,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::Task::{
    initialize_Init_Task, l_Task_mapList___redArg, runtime_initialize_Init_Task,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_getMaxHeartbeats, l_Lean_Exception_isRuntime, l_Lean_diagnostics,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_get_x21___redArg,
    l_Lean_PersistentArray_mapM___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toList___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg, l_Lean_PersistentHashMap_insert___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::{
    l_Lean_FileMap_toPosition, l_Lean_instInhabitedFileMap_default,
};
use crate::r#gen::Lean::Elab::InfoTree::Types::{
    l_Lean_Elab_instInhabitedInfoTree_default, l_Lean_Elab_instReprDocElabKind_repr,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqMVarId_beq, l_Lean_instBEqMVarId_beq___boxed, l_Lean_instHashableMVarId_hash,
    l_Lean_instHashableMVarId_hash___boxed, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_empty;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_MessageData_toString, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_Meta_ppExpr,
};
use crate::r#gen::Lean::Meta::PPGoal::{
    initialize_Lean_Meta_PPGoal, l_Lean_Meta_ppGoal, runtime_initialize_Lean_Meta_PPGoal,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_mkConstWithLevelParams___redArg;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::{
    initialize_Lean_ReservedNameAction, l_Lean_realizeGlobalConst,
    l_Lean_realizeGlobalConstNoOverload, l_Lean_realizeGlobalName,
    runtime_initialize_Lean_ReservedNameAction,
};
use crate::r#gen::Lean::Util::PPExt::l_Lean_ppTerm;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::l_Lean_inheritedTraceOptions;
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_get_num_heartbeats;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_dbg_to_string;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint8_once, lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
pub static l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1_value: LeanStringObject<
    24,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 77,
        97, 105, 110, 0,
    ],
};
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2_value: LeanStringObject<
    45,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 97, 114, 116, 105, 97, 108, 67, 111, 110,
        116, 101, 120, 116, 73, 110, 102, 111, 46, 109, 101, 114, 103, 101, 73, 110, 116, 111, 79,
        117, 116, 101, 114, 63, 0,
    ],
};
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3_value: LeanStringObject<
    45,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 99, 111, 109, 112, 108, 101,
        116, 101, 32, 73, 110, 102, 111, 84, 114, 101, 101, 32, 99, 111, 110, 116, 101, 120, 116,
        32, 105, 110, 102, 111, 46, 0,
    ],
};
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_CustomInfo_format___closed__0_value: LeanStringObject<13> =
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
        m_data: [91, 67, 117, 115, 116, 111, 109, 73, 110, 102, 111, 40, 0],
    };
static mut l_Lean_Elab_CustomInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CustomInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_CustomInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_CustomInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_CustomInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CustomInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_CustomInfo_format___closed__2_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [41, 93, 0],
    };
static mut l_Lean_Elab_CustomInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CustomInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_CustomInfo_format___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_CustomInfo_format___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_CustomInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CustomInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_instToFormatCustomInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_CustomInfo_format as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instToFormatCustomInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatCustomInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_instToFormatCustomInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatCustomInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110,
            32, 35, 0,
        ],
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value: LeanStringObject<11> =
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
        m_data: [60, 73, 110, 102, 111, 84, 114, 101, 101, 62, 0],
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14: u8 = 0;
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut LeanObject,
            72621647814721793 as *mut LeanObject,
            65793 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1: u64 = 0;
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 128, 160, 0]};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 128, 160, 33, 0]};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value:
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
    m_data: [32, 64, 32, 0],
};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 32, 0],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [91, 84, 101, 114, 109, 93, 32, 0],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [32, 0],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__6_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__7_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            40, 105, 115, 66, 105, 110, 100, 101, 114, 32, 58, 61, 32, 116, 114, 117, 101, 41, 32,
            0,
        ],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__8_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            60, 102, 97, 105, 108, 101, 100, 45, 116, 111, 45, 105, 110, 102, 101, 114, 45, 116,
            121, 112, 101, 62, 0,
        ],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_TermInfo_format___lam__0___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_TermInfo_format___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TermInfo_format___lam__0___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_PartialTermInfo_format___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            91, 80, 97, 114, 116, 105, 97, 108, 84, 101, 114, 109, 93, 32, 64, 32, 0,
        ],
    };
static mut l_Lean_Elab_PartialTermInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialTermInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_PartialTermInfo_format___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_PartialTermInfo_format___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_PartialTermInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialTermInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            91, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 45, 73, 100, 93, 32, 0,
        ],
    };
static mut l_Lean_Elab_CompletionInfo_format___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_CompletionInfo_format___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 58, 32, 0],
    };
static mut l_Lean_Elab_CompletionInfo_format___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___lam__0___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_CompletionInfo_format___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___closed__0_value: LeanStringObject<18> =
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
            91, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 45, 68, 111, 116, 93, 32, 0,
        ],
    };
static mut l_Lean_Elab_CompletionInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_CompletionInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            91, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 93, 32, 0,
        ],
    };
static mut l_Lean_Elab_CompletionInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_CompletionInfo_format___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_CompletionInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CompletionInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_CommandInfo_format___closed__0_value: LeanStringObject<13> =
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
        m_data: [91, 67, 111, 109, 109, 97, 110, 100, 93, 32, 64, 32, 0],
    };
static mut l_Lean_Elab_CommandInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CommandInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_CommandInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_CommandInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_CommandInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CommandInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_OptionInfo_format___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [91, 79, 112, 116, 105, 111, 110, 93, 32, 0],
    };
static mut l_Lean_Elab_OptionInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OptionInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_OptionInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_OptionInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_OptionInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_OptionInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ErrorNameInfo_format___closed__0_value: LeanStringObject<13> =
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
        m_data: [91, 69, 114, 114, 111, 114, 78, 97, 109, 101, 93, 32, 0],
    };
static mut l_Lean_Elab_ErrorNameInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorNameInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_ErrorNameInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorNameInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorNameInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorNameInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value: LeanStringObject<9> =
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
        m_data: [91, 70, 105, 101, 108, 100, 93, 32, 0],
    };
static mut l_Lean_Elab_FieldInfo_format___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_FieldInfo_format___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_FieldInfo_format___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FieldInfo_format___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_Elab_FieldInfo_format___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_FieldInfo_format___lam__0___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_FieldInfo_format___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FieldInfo_format___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [10, 0],
    };
static mut l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ContextInfo_ppGoals___closed__5_value: LeanStringObject<9> =
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
        m_data: [110, 111, 32, 103, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_ppGoals___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_ContextInfo_ppGoals___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ContextInfo_ppGoals___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ContextInfo_ppGoals___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ContextInfo_ppGoals___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_TacticInfo_format___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [91, 84, 97, 99, 116, 105, 99, 93, 32, 64, 32, 0],
    };
static mut l_Lean_Elab_TacticInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_TacticInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_TacticInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_TacticInfo_format___closed__2_value: LeanStringObject<9> =
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
        m_data: [10, 98, 101, 102, 111, 114, 101, 32, 0],
    };
static mut l_Lean_Elab_TacticInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_TacticInfo_format___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_TacticInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_TacticInfo_format___closed__4_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [10, 97, 102, 116, 101, 114, 32, 0],
    };
static mut l_Lean_Elab_TacticInfo_format___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_TacticInfo_format___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_TacticInfo_format___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TacticInfo_format___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_MacroExpansionInfo_format___closed__0_value: LeanStringObject<18> =
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
            91, 77, 97, 99, 114, 111, 69, 120, 112, 97, 110, 115, 105, 111, 110, 93, 10, 0,
        ],
    };
static mut l_Lean_Elab_MacroExpansionInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_MacroExpansionInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_MacroExpansionInfo_format___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_MacroExpansionInfo_format___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_MacroExpansionInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_MacroExpansionInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_MacroExpansionInfo_format___closed__2_value: LeanStringObject<7> =
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
        m_data: [10, 61, 61, 61, 62, 10, 0],
    };
static mut l_Lean_Elab_MacroExpansionInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_MacroExpansionInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_MacroExpansionInfo_format___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_MacroExpansionInfo_format___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_MacroExpansionInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_MacroExpansionInfo_format___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_UserWidgetInfo_format___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_UserWidgetInfo_format___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_UserWidgetInfo_format___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_UserWidgetInfo_format___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_UserWidgetInfo_format___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_UserWidgetInfo_format___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_UserWidgetInfo_format___closed__3_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            91, 85, 115, 101, 114, 87, 105, 100, 103, 101, 116, 93, 32, 0,
        ],
    };
static mut l_Lean_Elab_UserWidgetInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_UserWidgetInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_UserWidgetInfo_format___closed__4_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_UserWidgetInfo_format___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_UserWidgetInfo_format___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_UserWidgetInfo_format___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_FVarAliasInfo_format___closed__0_value: LeanStringObject<13> =
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
        m_data: [91, 70, 86, 97, 114, 65, 108, 105, 97, 115, 93, 32, 0],
    };
static mut l_Lean_Elab_FVarAliasInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FVarAliasInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_FVarAliasInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_FVarAliasInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_FVarAliasInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FVarAliasInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_FVarAliasInfo_format___closed__2_value: LeanStringObject<5> =
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
        m_data: [32, 45, 62, 32, 0],
    };
static mut l_Lean_Elab_FVarAliasInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FVarAliasInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_FVarAliasInfo_format___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_FVarAliasInfo_format___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_FVarAliasInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FVarAliasInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_FieldRedeclInfo_format___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            91, 70, 105, 101, 108, 100, 82, 101, 100, 101, 99, 108, 93, 32, 64, 32, 0,
        ],
    };
static mut l_Lean_Elab_FieldRedeclInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FieldRedeclInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_FieldRedeclInfo_format___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_FieldRedeclInfo_format___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_FieldRedeclInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_FieldRedeclInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0_value: LeanStringObject<9> =
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
        m_data: [91, 69, 114, 114, 111, 114, 58, 32, 0],
    };
static mut l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [93, 0],
    };
static mut l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
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
            91, 68, 101, 108, 97, 98, 84, 101, 114, 109, 93, 32, 64, 32, 0,
        ],
    };
static mut l_Lean_Elab_DelabTermInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DelabTermInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [10, 76, 111, 99, 97, 116, 105, 111, 110, 58, 32, 0],
    };
static mut l_Lean_Elab_DelabTermInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DelabTermInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__4_value: LeanStringObject<13> =
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
        m_data: [10, 68, 111, 99, 115, 116, 114, 105, 110, 103, 58, 32, 0],
    };
static mut l_Lean_Elab_DelabTermInfo_format___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DelabTermInfo_format___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__6_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [10, 69, 120, 112, 108, 105, 99, 105, 116, 58, 32, 0],
    };
static mut l_Lean_Elab_DelabTermInfo_format___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DelabTermInfo_format___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__8_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Elab_DelabTermInfo_format___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_DelabTermInfo_format___closed__9_value: LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Elab_DelabTermInfo_format___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DelabTermInfo_format___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_ChoiceInfo_format___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [91, 67, 104, 111, 105, 99, 101, 93, 32, 64, 32, 0],
    };
static mut l_Lean_Elab_ChoiceInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ChoiceInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_ChoiceInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ChoiceInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ChoiceInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ChoiceInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_DocInfo_format___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [91, 68, 111, 99, 93, 32, 0],
};
static mut l_Lean_Elab_DocInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_DocInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Elab_DocInfo_format___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Elab_DocInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_DocElabInfo_format___closed__0_value: LeanStringObject<11> =
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
        m_data: [91, 68, 111, 99, 69, 108, 97, 98, 93, 32, 0],
    };
static mut l_Lean_Elab_DocElabInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_DocElabInfo_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DocElabInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_DocElabInfo_format___closed__2_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [32, 40, 0],
    };
static mut l_Lean_Elab_DocElabInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_DocElabInfo_format___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DocElabInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_DocElabInfo_format___closed__4_value: LeanStringObject<5> =
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
        m_data: [41, 32, 64, 32, 0],
    };
static mut l_Lean_Elab_DocElabInfo_format___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_DocElabInfo_format___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DocElabInfo_format___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DocElabInfo_format___closed__5_value) as *mut LeanObject;
pub static l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_format___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_PartialContextInfo_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_format___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_format___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_PartialContextInfo_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_format___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 97, 114, 101, 110, 116, 91, 0],
    };
static mut l_Lean_Elab_PartialContextInfo_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_format___closed__3_value: LeanStringObject<15> =
    LeanStringObject {
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
            97, 117, 116, 111, 73, 109, 112, 108, 105, 99, 105, 116, 115, 91, 0,
        ],
    };
static mut l_Lean_Elab_PartialContextInfo_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_PartialContextInfo_format___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [35, 0],
    };
static mut l_Lean_Elab_PartialContextInfo_format___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialContextInfo_format___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_format___closed__0_value: LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 25,
    m_data: [
        226, 128, 162, 32, 60, 99, 111, 110, 116, 101, 120, 116, 45, 110, 111, 116, 45, 97, 118,
        97, 105, 108, 97, 98, 108, 101, 62, 0,
    ],
};
static mut l_Lean_Elab_InfoTree_format___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_format___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Elab_InfoTree_format___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_format___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [226, 128, 162, 32, 0],
};
static mut l_Lean_Elab_InfoTree_format___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_format___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Elab_InfoTree_format___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_format___closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [226, 128, 162, 32, 63, 0],
};
static mut l_Lean_Elab_InfoTree_format___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_InfoTree_format___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__4_value) as *mut LeanObject],
};
static mut l_Lean_Elab_InfoTree_format___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_InfoTree_format___closed__5_value) as *mut LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_getResetInfoTrees___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_getResetInfoTrees___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_getResetInfoTrees___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getResetInfoTrees___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withInfoContext_x27___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_withInfoContext_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_withInfoContext_x27___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instBEqMVarId_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instHashableMVarId_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 97, 115, 115, 105, 103, 110, 73, 110, 102,
            111, 72, 111, 108, 101, 73, 100, 0,
        ],
    };
static mut l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value: LeanStringObject<101> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 101,
        m_capacity: 101,
        m_length: 100,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101,
            97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 77, 97,
            105, 110, 46, 50, 51, 55, 57, 48, 56, 52, 56, 52, 50, 46, 95, 104, 121, 103, 67, 116,
            120, 46, 95, 104, 121, 103, 46, 49, 57, 46, 48, 32, 41, 46, 105, 115, 78, 111, 110,
            101, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_withEnableInfoTree___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_withEnableInfoTree___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_withEnableInfoTree___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0(
    mut v_____do__lift_4536_: *mut LeanObject,
    mut v_____do__lift_4537_: *mut LeanObject,
    mut v_____do__lift_4538_: *mut LeanObject,
    mut v_____do__lift_4539_: *mut LeanObject,
    mut v_____do__lift_4540_: *mut LeanObject,
    mut v_toPure_4541_: *mut LeanObject,
    mut v_____do__lift_4542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    v___x_4543_ = lean_box(0);
    v___x_4544_ = l_Lean_instInhabitedFileMap_default;
    v___x_4545_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_4545_, 0, v_____do__lift_4536_);
    lean_ctor_set(v___x_4545_, 1, v___x_4543_);
    lean_ctor_set(v___x_4545_, 2, v___x_4544_);
    lean_ctor_set(v___x_4545_, 3, v_____do__lift_4537_);
    lean_ctor_set(v___x_4545_, 4, v_____do__lift_4538_);
    lean_ctor_set(v___x_4545_, 5, v_____do__lift_4539_);
    lean_ctor_set(v___x_4545_, 6, v_____do__lift_4540_);
    lean_ctor_set(v___x_4545_, 7, v_____do__lift_4542_);
    v___x_4546_ = lean_apply_2(v_toPure_4541_, lean_box(0), v___x_4545_);
    return v___x_4546_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1(
    mut v_inst_4547_: *mut LeanObject,
    mut v_____do__lift_4548_: *mut LeanObject,
    mut v_____do__lift_4549_: *mut LeanObject,
    mut v_____do__lift_4550_: *mut LeanObject,
    mut v_____do__lift_4551_: *mut LeanObject,
    mut v_toPure_4552_: *mut LeanObject,
    mut v_toBind_4553_: *mut LeanObject,
    mut v_____do__lift_4554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getNGen_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v_getNGen_4555_ = lean_ctor_get(v_inst_4547_, 0);
    lean_inc(v_getNGen_4555_);
    lean_dec_ref(v_inst_4547_);
    v___f_4556_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_4556_, 0, v_____do__lift_4548_);
    lean_closure_set(v___f_4556_, 1, v_____do__lift_4549_);
    lean_closure_set(v___f_4556_, 2, v_____do__lift_4550_);
    lean_closure_set(v___f_4556_, 3, v_____do__lift_4551_);
    lean_closure_set(v___f_4556_, 4, v_____do__lift_4554_);
    lean_closure_set(v___f_4556_, 5, v_toPure_4552_);
    v___x_4557_ = lean_apply_4(
        v_toBind_4553_,
        lean_box(0),
        lean_box(0),
        v_getNGen_4555_,
        v___f_4556_,
    );
    return v___x_4557_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2(
    mut v_inst_4558_: *mut LeanObject,
    mut v_____do__lift_4559_: *mut LeanObject,
    mut v_____do__lift_4560_: *mut LeanObject,
    mut v_____do__lift_4561_: *mut LeanObject,
    mut v_toPure_4562_: *mut LeanObject,
    mut v_toBind_4563_: *mut LeanObject,
    mut v_getOpenDecls_4564_: *mut LeanObject,
    mut v_____do__lift_4565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_4563_);
    v___f_4566_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_4566_, 0, v_inst_4558_);
    lean_closure_set(v___f_4566_, 1, v_____do__lift_4559_);
    lean_closure_set(v___f_4566_, 2, v_____do__lift_4560_);
    lean_closure_set(v___f_4566_, 3, v_____do__lift_4561_);
    lean_closure_set(v___f_4566_, 4, v_____do__lift_4565_);
    lean_closure_set(v___f_4566_, 5, v_toPure_4562_);
    lean_closure_set(v___f_4566_, 6, v_toBind_4563_);
    v___x_4567_ = lean_apply_4(
        v_toBind_4563_,
        lean_box(0),
        lean_box(0),
        v_getOpenDecls_4564_,
        v___f_4566_,
    );
    return v___x_4567_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3(
    mut v_inst_4568_: *mut LeanObject,
    mut v_inst_4569_: *mut LeanObject,
    mut v_____do__lift_4570_: *mut LeanObject,
    mut v_____do__lift_4571_: *mut LeanObject,
    mut v_toPure_4572_: *mut LeanObject,
    mut v_toBind_4573_: *mut LeanObject,
    mut v_____do__lift_4574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCurrNamespace_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_4575_ = lean_ctor_get(v_inst_4568_, 0);
    lean_inc(v_getCurrNamespace_4575_);
    v_getOpenDecls_4576_ = lean_ctor_get(v_inst_4568_, 1);
    lean_inc(v_getOpenDecls_4576_);
    lean_dec_ref(v_inst_4568_);
    lean_inc(v_toBind_4573_);
    v___f_4577_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_4577_, 0, v_inst_4569_);
    lean_closure_set(v___f_4577_, 1, v_____do__lift_4570_);
    lean_closure_set(v___f_4577_, 2, v_____do__lift_4571_);
    lean_closure_set(v___f_4577_, 3, v_____do__lift_4574_);
    lean_closure_set(v___f_4577_, 4, v_toPure_4572_);
    lean_closure_set(v___f_4577_, 5, v_toBind_4573_);
    lean_closure_set(v___f_4577_, 6, v_getOpenDecls_4576_);
    v___x_4578_ = lean_apply_4(
        v_toBind_4573_,
        lean_box(0),
        lean_box(0),
        v_getCurrNamespace_4575_,
        v___f_4577_,
    );
    return v___x_4578_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4(
    mut v_inst_4579_: *mut LeanObject,
    mut v_inst_4580_: *mut LeanObject,
    mut v_____do__lift_4581_: *mut LeanObject,
    mut v_toPure_4582_: *mut LeanObject,
    mut v_toBind_4583_: *mut LeanObject,
    mut v_inst_4584_: *mut LeanObject,
    mut v_____do__lift_4585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_4583_);
    v___f_4586_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_4586_, 0, v_inst_4579_);
    lean_closure_set(v___f_4586_, 1, v_inst_4580_);
    lean_closure_set(v___f_4586_, 2, v_____do__lift_4581_);
    lean_closure_set(v___f_4586_, 3, v_____do__lift_4585_);
    lean_closure_set(v___f_4586_, 4, v_toPure_4582_);
    lean_closure_set(v___f_4586_, 5, v_toBind_4583_);
    v___x_4587_ = lean_apply_4(
        v_toBind_4583_,
        lean_box(0),
        lean_box(0),
        v_inst_4584_,
        v___f_4586_,
    );
    return v___x_4587_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5(
    mut v_inst_4588_: *mut LeanObject,
    mut v_inst_4589_: *mut LeanObject,
    mut v_inst_4590_: *mut LeanObject,
    mut v_toPure_4591_: *mut LeanObject,
    mut v_toBind_4592_: *mut LeanObject,
    mut v_inst_4593_: *mut LeanObject,
    mut v_____do__lift_4594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getMCtx_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    v_getMCtx_4595_ = lean_ctor_get(v_inst_4588_, 0);
    lean_inc(v_getMCtx_4595_);
    lean_dec_ref(v_inst_4588_);
    lean_inc(v_toBind_4592_);
    v___f_4596_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_4596_, 0, v_inst_4589_);
    lean_closure_set(v___f_4596_, 1, v_inst_4590_);
    lean_closure_set(v___f_4596_, 2, v_____do__lift_4594_);
    lean_closure_set(v___f_4596_, 3, v_toPure_4591_);
    lean_closure_set(v___f_4596_, 4, v_toBind_4592_);
    lean_closure_set(v___f_4596_, 5, v_inst_4593_);
    v___x_4597_ = lean_apply_4(
        v_toBind_4592_,
        lean_box(0),
        lean_box(0),
        v_getMCtx_4595_,
        v___f_4596_,
    );
    return v___x_4597_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(
    mut v_inst_4598_: *mut LeanObject,
    mut v_inst_4599_: *mut LeanObject,
    mut v_inst_4600_: *mut LeanObject,
    mut v_inst_4601_: *mut LeanObject,
    mut v_inst_4602_: *mut LeanObject,
    mut v_inst_4603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4604_ = lean_ctor_get(v_inst_4598_, 0);
    lean_inc_ref(v_toApplicative_4604_);
    v_toBind_4605_ = lean_ctor_get(v_inst_4598_, 1);
    lean_inc_n(v_toBind_4605_, 2);
    lean_dec_ref(v_inst_4598_);
    v_getEnv_4606_ = lean_ctor_get(v_inst_4599_, 0);
    lean_inc(v_getEnv_4606_);
    lean_dec_ref(v_inst_4599_);
    v_toPure_4607_ = lean_ctor_get(v_toApplicative_4604_, 1);
    lean_inc(v_toPure_4607_);
    lean_dec_ref(v_toApplicative_4604_);
    v___f_4608_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_4608_, 0, v_inst_4600_);
    lean_closure_set(v___f_4608_, 1, v_inst_4602_);
    lean_closure_set(v___f_4608_, 2, v_inst_4603_);
    lean_closure_set(v___f_4608_, 3, v_toPure_4607_);
    lean_closure_set(v___f_4608_, 4, v_toBind_4605_);
    lean_closure_set(v___f_4608_, 5, v_inst_4601_);
    v___x_4609_ = lean_apply_4(
        v_toBind_4605_,
        lean_box(0),
        lean_box(0),
        v_getEnv_4606_,
        v___f_4608_,
    );
    return v___x_4609_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap(
    mut v_m_4610_: *mut LeanObject,
    mut v_inst_4611_: *mut LeanObject,
    mut v_inst_4612_: *mut LeanObject,
    mut v_inst_4613_: *mut LeanObject,
    mut v_inst_4614_: *mut LeanObject,
    mut v_inst_4615_: *mut LeanObject,
    mut v_inst_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    v___x_4617_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(
        v_inst_4611_,
        v_inst_4612_,
        v_inst_4613_,
        v_inst_4614_,
        v_inst_4615_,
        v_inst_4616_,
    );
    return v___x_4617_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___redArg___lam__0(
    mut v_ctx_4618_: *mut LeanObject,
    mut v_toPure_4619_: *mut LeanObject,
    mut v_____do__lift_4620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdEnv_x3f_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4630_: u8 = 0;
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4635_: u8 = 0;
    let mut v_unused_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_4621_ = lean_ctor_get(v_ctx_4618_, 0);
                v_cmdEnv_x3f_4622_ = lean_ctor_get(v_ctx_4618_, 1);
                v_mctx_4623_ = lean_ctor_get(v_ctx_4618_, 3);
                v_options_4624_ = lean_ctor_get(v_ctx_4618_, 4);
                v_currNamespace_4625_ = lean_ctor_get(v_ctx_4618_, 5);
                v_openDecls_4626_ = lean_ctor_get(v_ctx_4618_, 6);
                v_ngen_4627_ = lean_ctor_get(v_ctx_4618_, 7);
                v_isSharedCheck_4635_ = (!lean_is_exclusive(v_ctx_4618_)) as u8;
                if v_isSharedCheck_4635_ == 0 {
                    v_unused_4636_ = lean_ctor_get(v_ctx_4618_, 2);
                    lean_dec(v_unused_4636_);
                    v___x_4629_ = v_ctx_4618_;
                    v_isShared_4630_ = v_isSharedCheck_4635_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ngen_4627_);
                    lean_inc(v_openDecls_4626_);
                    lean_inc(v_currNamespace_4625_);
                    lean_inc(v_options_4624_);
                    lean_inc(v_mctx_4623_);
                    lean_inc(v_cmdEnv_x3f_4622_);
                    lean_inc(v_env_4621_);
                    lean_dec(v_ctx_4618_);
                    v___x_4629_ = lean_box(0);
                    v_isShared_4630_ = v_isSharedCheck_4635_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4630_ == 0 {
                    lean_ctor_set(v___x_4629_, 2, v_____do__lift_4620_);
                    v___x_4632_ = v___x_4629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_env_4621_);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 1, v_cmdEnv_x3f_4622_);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 2, v_____do__lift_4620_);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 3, v_mctx_4623_);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 4, v_options_4624_);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 5, v_currNamespace_4625_);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 6, v_openDecls_4626_);
                    lean_ctor_set(v_reuseFailAlloc_4634_, 7, v_ngen_4627_);
                    v___x_4632_ = v_reuseFailAlloc_4634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4633_ = lean_apply_2(v_toPure_4619_, lean_box(0), v___x_4632_);
                return v___x_4633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___redArg___lam__1(
    mut v_toPure_4637_: *mut LeanObject,
    mut v_toBind_4638_: *mut LeanObject,
    mut v_inst_4639_: *mut LeanObject,
    mut v_ctx_4640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    v___f_4641_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_save___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4641_, 0, v_ctx_4640_);
    lean_closure_set(v___f_4641_, 1, v_toPure_4637_);
    v___x_4642_ = lean_apply_4(
        v_toBind_4638_,
        lean_box(0),
        lean_box(0),
        v_inst_4639_,
        v___f_4641_,
    );
    return v___x_4642_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___redArg(
    mut v_inst_4643_: *mut LeanObject,
    mut v_inst_4644_: *mut LeanObject,
    mut v_inst_4645_: *mut LeanObject,
    mut v_inst_4646_: *mut LeanObject,
    mut v_inst_4647_: *mut LeanObject,
    mut v_inst_4648_: *mut LeanObject,
    mut v_inst_4649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4650_ = lean_ctor_get(v_inst_4643_, 0);
    v_toBind_4651_ = lean_ctor_get(v_inst_4643_, 1);
    lean_inc_n(v_toBind_4651_, 2);
    v_toPure_4652_ = lean_ctor_get(v_toApplicative_4650_, 1);
    lean_inc(v_toPure_4652_);
    v___x_4653_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(
        v_inst_4643_,
        v_inst_4644_,
        v_inst_4645_,
        v_inst_4646_,
        v_inst_4647_,
        v_inst_4648_,
    );
    v___f_4654_ = lean_alloc_closure(
        l_Lean_Elab_CommandContextInfo_save___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4654_, 0, v_toPure_4652_);
    lean_closure_set(v___f_4654_, 1, v_toBind_4651_);
    lean_closure_set(v___f_4654_, 2, v_inst_4649_);
    v___x_4655_ = lean_apply_4(
        v_toBind_4651_,
        lean_box(0),
        lean_box(0),
        v___x_4653_,
        v___f_4654_,
    );
    return v___x_4655_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save(
    mut v_m_4656_: *mut LeanObject,
    mut v_inst_4657_: *mut LeanObject,
    mut v_inst_4658_: *mut LeanObject,
    mut v_inst_4659_: *mut LeanObject,
    mut v_inst_4660_: *mut LeanObject,
    mut v_inst_4661_: *mut LeanObject,
    mut v_inst_4662_: *mut LeanObject,
    mut v_inst_4663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    v___x_4664_ = l_Lean_Elab_CommandContextInfo_save___redArg(
        v_inst_4657_,
        v_inst_4658_,
        v_inst_4659_,
        v_inst_4660_,
        v_inst_4661_,
        v_inst_4662_,
        v_inst_4663_,
    );
    return v___x_4664_;
}
pub unsafe fn l_panic___at___00Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f_spec__0(
    mut v_msg_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    v___x_4666_ = lean_box(0);
    v___x_4667_ = lean_panic_fn_borrowed(v___x_4666_, v_msg_4665_);
    return v___x_4667_;
}
pub unsafe fn _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4()
-> *mut LeanObject {
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    v___x_4673_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3;
    v___x_4674_ = lean_unsigned_to_nat(4);
    v___x_4675_ = lean_unsigned_to_nat(52);
    v___x_4676_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2;
    v___x_4677_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1;
    v___x_4678_ = l_mkPanicMessageWithDecl(
        v___x_4677_,
        v___x_4676_,
        v___x_4675_,
        v___x_4674_,
        v___x_4673_,
    );
    return v___x_4678_;
}
pub unsafe fn _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5()
-> *mut LeanObject {
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    v___x_4679_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__3;
    v___x_4680_ = lean_unsigned_to_nat(4);
    v___x_4681_ = lean_unsigned_to_nat(54);
    v___x_4682_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__2;
    v___x_4683_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1;
    v___x_4684_ = l_mkPanicMessageWithDecl(
        v___x_4683_,
        v___x_4682_,
        v___x_4681_,
        v___x_4680_,
        v___x_4679_,
    );
    return v___x_4684_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
    mut v_x_4685_: *mut LeanObject,
    mut v_x_4686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4690_: u8 = 0;
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v_info_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v_env_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdEnv_x3f_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4713_: u8 = 0;
    let mut v_toCommandContextInfo_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_x3f_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_autoImplicits_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v___y_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdEnv_x3f_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut v_isSharedCheck_4733_: u8 = 0;
    let mut v_isSharedCheck_4734_: u8 = 0;
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4740_: u8 = 0;
    let mut v_parentDecl_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4744_: u8 = 0;
    let mut v_toCommandContextInfo_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_autoImplicits_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut v_unused_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v_autoImplicits_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_x3f_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4781_: u8 = 0;
    let mut v_unused_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_4685_) {
                    0 => {
                        if lean_obj_tag(v_x_4686_) == 0 {
                            v_info_4687_ = lean_ctor_get(v_x_4685_, 0);
                            v_isSharedCheck_4697_ = (!lean_is_exclusive(v_x_4685_)) as u8;
                            if v_isSharedCheck_4697_ == 0 {
                                v___x_4689_ = v_x_4685_;
                                v_isShared_4690_ = v_isSharedCheck_4697_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_info_4687_);
                                lean_dec(v_x_4685_);
                                v___x_4689_ = lean_box(0);
                                v_isShared_4690_ = v_isSharedCheck_4697_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_info_4698_ = lean_ctor_get(v_x_4685_, 0);
                            lean_inc_ref(v_info_4698_);
                            lean_dec_ref_known(v_x_4685_, 1);
                            v_val_4699_ = lean_ctor_get(v_x_4686_, 0);
                            v_isSharedCheck_4734_ = (!lean_is_exclusive(v_x_4686_)) as u8;
                            if v_isSharedCheck_4734_ == 0 {
                                v___x_4701_ = v_x_4686_;
                                v_isShared_4702_ = v_isSharedCheck_4734_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_val_4699_);
                                lean_dec(v_x_4686_);
                                v___x_4701_ = lean_box(0);
                                v_isShared_4702_ = v_isSharedCheck_4734_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    1 => {
                        if lean_obj_tag(v_x_4686_) == 0 {
                            lean_dec_ref_known(v_x_4685_, 1);
                            v___x_4735_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4_once), _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__4);
                            v___x_4736_ = l_panic___at___00Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f_spec__0(v___x_4735_);
                            return v___x_4736_;
                        } else {
                            v_val_4737_ = lean_ctor_get(v_x_4686_, 0);
                            v_isSharedCheck_4762_ = (!lean_is_exclusive(v_x_4686_)) as u8;
                            if v_isSharedCheck_4762_ == 0 {
                                v___x_4739_ = v_x_4686_;
                                v_isShared_4740_ = v_isSharedCheck_4762_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_val_4737_);
                                lean_dec(v_x_4686_);
                                v___x_4739_ = lean_box(0);
                                v_isShared_4740_ = v_isSharedCheck_4762_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                    _ => {
                        if lean_obj_tag(v_x_4686_) == 0 {
                            lean_dec_ref_known(v_x_4685_, 1);
                            v___x_4763_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5_once), _init_l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__5);
                            v___x_4764_ = l_panic___at___00Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f_spec__0(v___x_4763_);
                            return v___x_4764_;
                        } else {
                            v_val_4765_ = lean_ctor_get(v_x_4686_, 0);
                            v_isSharedCheck_4783_ = (!lean_is_exclusive(v_x_4686_)) as u8;
                            if v_isSharedCheck_4783_ == 0 {
                                v___x_4767_ = v_x_4686_;
                                v_isShared_4768_ = v_isSharedCheck_4783_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_val_4765_);
                                lean_dec(v_x_4686_);
                                v___x_4767_ = lean_box(0);
                                v_isShared_4768_ = v_isSharedCheck_4783_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4691_ = lean_box(0);
                v___x_4692_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__0;
                v___x_4693_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4693_, 0, v_info_4687_);
                lean_ctor_set(v___x_4693_, 1, v___x_4691_);
                lean_ctor_set(v___x_4693_, 2, v___x_4692_);
                if v_isShared_4690_ == 0 {
                    lean_ctor_set_tag(v___x_4689_, 1);
                    lean_ctor_set(v___x_4689_, 0, v___x_4693_);
                    v___x_4695_ = v___x_4689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
                    v___x_4695_ = v_reuseFailAlloc_4696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4695_;
            }
            3 => {
                v_env_4703_ = lean_ctor_get(v_info_4698_, 0);
                v_cmdEnv_x3f_4704_ = lean_ctor_get(v_info_4698_, 1);
                v_fileMap_4705_ = lean_ctor_get(v_info_4698_, 2);
                v_mctx_4706_ = lean_ctor_get(v_info_4698_, 3);
                v_options_4707_ = lean_ctor_get(v_info_4698_, 4);
                v_currNamespace_4708_ = lean_ctor_get(v_info_4698_, 5);
                v_openDecls_4709_ = lean_ctor_get(v_info_4698_, 6);
                v_ngen_4710_ = lean_ctor_get(v_info_4698_, 7);
                v_isSharedCheck_4733_ = (!lean_is_exclusive(v_info_4698_)) as u8;
                if v_isSharedCheck_4733_ == 0 {
                    v___x_4712_ = v_info_4698_;
                    v_isShared_4713_ = v_isSharedCheck_4733_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_ngen_4710_);
                    lean_inc(v_openDecls_4709_);
                    lean_inc(v_currNamespace_4708_);
                    lean_inc(v_options_4707_);
                    lean_inc(v_mctx_4706_);
                    lean_inc(v_fileMap_4705_);
                    lean_inc(v_cmdEnv_x3f_4704_);
                    lean_inc(v_env_4703_);
                    lean_dec(v_info_4698_);
                    v___x_4712_ = lean_box(0);
                    v_isShared_4713_ = v_isSharedCheck_4733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toCommandContextInfo_4714_ = lean_ctor_get(v_val_4699_, 0);
                v_parentDecl_x3f_4715_ = lean_ctor_get(v_val_4699_, 1);
                v_autoImplicits_4716_ = lean_ctor_get(v_val_4699_, 2);
                v_isSharedCheck_4732_ = (!lean_is_exclusive(v_val_4699_)) as u8;
                if v_isSharedCheck_4732_ == 0 {
                    v___x_4718_ = v_val_4699_;
                    v_isShared_4719_ = v_isSharedCheck_4732_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_autoImplicits_4716_);
                    lean_inc(v_parentDecl_x3f_4715_);
                    lean_inc(v_toCommandContextInfo_4714_);
                    lean_dec(v_val_4699_);
                    v___x_4718_ = lean_box(0);
                    v_isShared_4719_ = v_isSharedCheck_4732_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_cmdEnv_x3f_4731_ = lean_ctor_get(v_toCommandContextInfo_4714_, 1);
                lean_inc(v_cmdEnv_x3f_4731_);
                lean_dec_ref(v_toCommandContextInfo_4714_);
                if lean_obj_tag(v_cmdEnv_x3f_4731_) == 0 {
                    v___y_4721_ = v_cmdEnv_x3f_4704_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_cmdEnv_x3f_4704_);
                    v___y_4721_ = v_cmdEnv_x3f_4731_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4713_ == 0 {
                    lean_ctor_set(v___x_4712_, 1, v___y_4721_);
                    v___x_4723_ = v___x_4712_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_env_4703_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 1, v___y_4721_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_fileMap_4705_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_mctx_4706_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_options_4707_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 5, v_currNamespace_4708_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 6, v_openDecls_4709_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 7, v_ngen_4710_);
                    v___x_4723_ = v_reuseFailAlloc_4730_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4719_ == 0 {
                    lean_ctor_set(v___x_4718_, 0, v___x_4723_);
                    v___x_4725_ = v___x_4718_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4723_);
                    lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_parentDecl_x3f_4715_);
                    lean_ctor_set(v_reuseFailAlloc_4729_, 2, v_autoImplicits_4716_);
                    v___x_4725_ = v_reuseFailAlloc_4729_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4702_ == 0 {
                    lean_ctor_set(v___x_4701_, 0, v___x_4725_);
                    v___x_4727_ = v___x_4701_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4725_);
                    v___x_4727_ = v_reuseFailAlloc_4728_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4727_;
            }
            10 => {
                v_parentDecl_4741_ = lean_ctor_get(v_x_4685_, 0);
                v_isSharedCheck_4761_ = (!lean_is_exclusive(v_x_4685_)) as u8;
                if v_isSharedCheck_4761_ == 0 {
                    v___x_4743_ = v_x_4685_;
                    v_isShared_4744_ = v_isSharedCheck_4761_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_parentDecl_4741_);
                    lean_dec(v_x_4685_);
                    v___x_4743_ = lean_box(0);
                    v_isShared_4744_ = v_isSharedCheck_4761_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_toCommandContextInfo_4745_ = lean_ctor_get(v_val_4737_, 0);
                v_autoImplicits_4746_ = lean_ctor_get(v_val_4737_, 2);
                v_isSharedCheck_4759_ = (!lean_is_exclusive(v_val_4737_)) as u8;
                if v_isSharedCheck_4759_ == 0 {
                    v_unused_4760_ = lean_ctor_get(v_val_4737_, 1);
                    lean_dec(v_unused_4760_);
                    v___x_4748_ = v_val_4737_;
                    v_isShared_4749_ = v_isSharedCheck_4759_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_autoImplicits_4746_);
                    lean_inc(v_toCommandContextInfo_4745_);
                    lean_dec(v_val_4737_);
                    v___x_4748_ = lean_box(0);
                    v_isShared_4749_ = v_isSharedCheck_4759_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4740_ == 0 {
                    lean_ctor_set(v___x_4739_, 0, v_parentDecl_4741_);
                    v___x_4751_ = v___x_4739_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_parentDecl_4741_);
                    v___x_4751_ = v_reuseFailAlloc_4758_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4749_ == 0 {
                    lean_ctor_set(v___x_4748_, 1, v___x_4751_);
                    v___x_4753_ = v___x_4748_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_toCommandContextInfo_4745_);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 1, v___x_4751_);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_autoImplicits_4746_);
                    v___x_4753_ = v_reuseFailAlloc_4757_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_4744_ == 0 {
                    lean_ctor_set(v___x_4743_, 0, v___x_4753_);
                    v___x_4755_ = v___x_4743_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4753_);
                    v___x_4755_ = v_reuseFailAlloc_4756_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4755_;
            }
            16 => {
                v_autoImplicits_4769_ = lean_ctor_get(v_x_4685_, 0);
                lean_inc_ref(v_autoImplicits_4769_);
                lean_dec_ref_known(v_x_4685_, 1);
                v_toCommandContextInfo_4770_ = lean_ctor_get(v_val_4765_, 0);
                v_parentDecl_x3f_4771_ = lean_ctor_get(v_val_4765_, 1);
                v_isSharedCheck_4781_ = (!lean_is_exclusive(v_val_4765_)) as u8;
                if v_isSharedCheck_4781_ == 0 {
                    v_unused_4782_ = lean_ctor_get(v_val_4765_, 2);
                    lean_dec(v_unused_4782_);
                    v___x_4773_ = v_val_4765_;
                    v_isShared_4774_ = v_isSharedCheck_4781_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_parentDecl_x3f_4771_);
                    lean_inc(v_toCommandContextInfo_4770_);
                    lean_dec(v_val_4765_);
                    v___x_4773_ = lean_box(0);
                    v_isShared_4774_ = v_isSharedCheck_4781_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4774_ == 0 {
                    lean_ctor_set(v___x_4773_, 2, v_autoImplicits_4769_);
                    v___x_4776_ = v___x_4773_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_toCommandContextInfo_4770_);
                    lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_parentDecl_x3f_4771_);
                    lean_ctor_set(v_reuseFailAlloc_4780_, 2, v_autoImplicits_4769_);
                    v___x_4776_ = v_reuseFailAlloc_4780_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_4768_ == 0 {
                    lean_ctor_set(v___x_4767_, 0, v___x_4776_);
                    v___x_4778_ = v___x_4767_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
                    v___x_4778_ = v_reuseFailAlloc_4779_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_stx(mut v_x_4784_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_4784_) == 0 {
        let mut v_termInfo_4785_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toElabInfo_4786_: *mut LeanObject = core::ptr::null_mut();
        let mut v_stx_4787_: *mut LeanObject = core::ptr::null_mut();
        v_termInfo_4785_ = lean_ctor_get(v_x_4784_, 0);
        v_toElabInfo_4786_ = lean_ctor_get(v_termInfo_4785_, 0);
        v_stx_4787_ = lean_ctor_get(v_toElabInfo_4786_, 1);
        lean_inc(v_stx_4787_);
        return v_stx_4787_;
    } else {
        let mut v_stx_4788_: *mut LeanObject = core::ptr::null_mut();
        v_stx_4788_ = lean_ctor_get(v_x_4784_, 0);
        lean_inc(v_stx_4788_);
        return v_stx_4788_;
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_stx___boxed(
    mut v_x_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4790_: *mut LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_Lean_Elab_CompletionInfo_stx(v_x_4789_);
    lean_dec_ref(v_x_4789_);
    return v_res_4790_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_lctx(mut v_x_4791_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4791_) {
        0 => {
            let mut v_termInfo_4792_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lctx_4793_: *mut LeanObject = core::ptr::null_mut();
            v_termInfo_4792_ = lean_ctor_get(v_x_4791_, 0);
            v_lctx_4793_ = lean_ctor_get(v_termInfo_4792_, 1);
            lean_inc_ref(v_lctx_4793_);
            return v_lctx_4793_;
        }
        1 => {
            let mut v_lctx_4794_: *mut LeanObject = core::ptr::null_mut();
            v_lctx_4794_ = lean_ctor_get(v_x_4791_, 2);
            lean_inc_ref(v_lctx_4794_);
            return v_lctx_4794_;
        }
        2 => {
            let mut v_lctx_4795_: *mut LeanObject = core::ptr::null_mut();
            v_lctx_4795_ = lean_ctor_get(v_x_4791_, 2);
            lean_inc_ref(v_lctx_4795_);
            return v_lctx_4795_;
        }
        3 => {
            let mut v_lctx_4796_: *mut LeanObject = core::ptr::null_mut();
            v_lctx_4796_ = lean_ctor_get(v_x_4791_, 2);
            lean_inc_ref(v_lctx_4796_);
            return v_lctx_4796_;
        }
        _ => {
            let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
            v___x_4797_ = l_Lean_LocalContext_empty;
            return v___x_4797_;
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_lctx___boxed(
    mut v_x_4798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4799_: *mut LeanObject = core::ptr::null_mut();
    v_res_4799_ = l_Lean_Elab_CompletionInfo_lctx(v_x_4798_);
    lean_dec_ref(v_x_4798_);
    return v_res_4799_;
}
pub unsafe fn l_Lean_Elab_CustomInfo_format(mut v_x_4806_: *mut LeanObject) -> *mut LeanObject {
    let mut v_value_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: u8 = 0;
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4821_: u8 = 0;
    let mut v_unused_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_4807_ = lean_ctor_get(v_x_4806_, 1);
                v_isSharedCheck_4821_ = (!lean_is_exclusive(v_x_4806_)) as u8;
                if v_isSharedCheck_4821_ == 0 {
                    v_unused_4822_ = lean_ctor_get(v_x_4806_, 0);
                    lean_dec(v_unused_4822_);
                    v___x_4809_ = v_x_4806_;
                    v_isShared_4810_ = v_isSharedCheck_4821_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_value_4807_);
                    lean_dec(v_x_4806_);
                    v___x_4809_ = lean_box(0);
                    v_isShared_4810_ = v_isSharedCheck_4821_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4811_ = l_Lean_Elab_CustomInfo_format___closed__1;
                v___x_4812_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_4807_);
                lean_dec(v_value_4807_);
                v___x_4813_ = 1;
                v___x_4814_ = l_Lean_Name_toString(v___x_4812_, v___x_4813_);
                v___x_4815_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4815_, 0, v___x_4814_);
                if v_isShared_4810_ == 0 {
                    lean_ctor_set_tag(v___x_4809_, 5);
                    lean_ctor_set(v___x_4809_, 1, v___x_4815_);
                    lean_ctor_set(v___x_4809_, 0, v___x_4811_);
                    v___x_4817_ = v___x_4809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4820_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4811_);
                    lean_ctor_set(v_reuseFailAlloc_4820_, 1, v___x_4815_);
                    v___x_4817_ = v_reuseFailAlloc_4820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4818_ = l_Lean_Elab_CustomInfo_format___closed__3;
                v___x_4819_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4819_, 0, v___x_4817_);
                lean_ctor_set(v___x_4819_, 1, v___x_4818_);
                return v___x_4819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1(
    mut v_p_4828_: *mut LeanObject,
    mut v_as_4829_: *mut LeanObject,
    mut v_sz_4830_: usize,
    mut v_i_4831_: usize,
    mut v_b_4832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4833_: u8 = 0;
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: usize = 0;
    let mut v___x_4841_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4833_ = lean_usize_dec_lt(v_i_4831_, v_sz_4830_);
                if v___x_4833_ == 0 {
                    lean_dec_ref(v_p_4828_);
                    lean_inc_ref(v_b_4832_);
                    return v_b_4832_;
                } else {
                    v___x_4834_ = lean_box(0);
                    v_a_4835_ = lean_array_uget_borrowed(v_as_4829_, v_i_4831_);
                    lean_inc_ref(v_p_4828_);
                    v___x_4836_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(v_p_4828_, v_a_4835_);
                    if lean_obj_tag(v___x_4836_) == 1 {
                        lean_dec_ref(v_p_4828_);
                        v___x_4837_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4837_, 0, v___x_4836_);
                        v___x_4838_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4838_, 0, v___x_4837_);
                        lean_ctor_set(v___x_4838_, 1, v___x_4834_);
                        return v___x_4838_;
                    } else {
                        lean_dec(v___x_4836_);
                        v___x_4839_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0;
                        v___x_4840_ = 1usize;
                        v___x_4841_ = lean_usize_add(v_i_4831_, v___x_4840_);
                        v_i_4831_ = v___x_4841_;
                        v_b_4832_ = v___x_4839_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(
    mut v_p_4843_: *mut LeanObject,
    mut v_as_4844_: *mut LeanObject,
    mut v_sz_4845_: usize,
    mut v_i_4846_: usize,
    mut v_b_4847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4848_: u8 = 0;
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: usize = 0;
    let mut v___x_4856_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4848_ = lean_usize_dec_lt(v_i_4846_, v_sz_4845_);
                if v___x_4848_ == 0 {
                    lean_dec_ref(v_p_4843_);
                    lean_inc_ref(v_b_4847_);
                    return v_b_4847_;
                } else {
                    v___x_4849_ = lean_box(0);
                    v_a_4850_ = lean_array_uget_borrowed(v_as_4844_, v_i_4846_);
                    lean_inc(v_a_4850_);
                    lean_inc_ref(v_p_4843_);
                    v___x_4851_ = l_Lean_Elab_InfoTree_findInfo_x3f(v_p_4843_, v_a_4850_);
                    if lean_obj_tag(v___x_4851_) == 1 {
                        lean_dec_ref(v_p_4843_);
                        v___x_4852_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4852_, 0, v___x_4851_);
                        v___x_4853_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4853_, 0, v___x_4852_);
                        lean_ctor_set(v___x_4853_, 1, v___x_4849_);
                        return v___x_4853_;
                    } else {
                        lean_dec(v___x_4851_);
                        v___x_4854_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0;
                        v___x_4855_ = 1usize;
                        v___x_4856_ = lean_usize_add(v_i_4846_, v___x_4855_);
                        v_i_4846_ = v___x_4856_;
                        v_b_4847_ = v___x_4854_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(
    mut v_p_4858_: *mut LeanObject,
    mut v_x_4859_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4859_) == 0 {
        let mut v_cs_4860_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4863_: usize = 0;
        let mut v___x_4864_: usize = 0;
        let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4866_: *mut LeanObject = core::ptr::null_mut();
        v_cs_4860_ = lean_ctor_get(v_x_4859_, 0);
        v___x_4861_ = lean_box(0);
        v___x_4862_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0;
        v_sz_4863_ = lean_array_size(v_cs_4860_);
        v___x_4864_ = 0usize;
        v___x_4865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1(v_p_4858_, v_cs_4860_, v_sz_4863_, v___x_4864_, v___x_4862_);
        v_fst_4866_ = lean_ctor_get(v___x_4865_, 0);
        lean_inc(v_fst_4866_);
        lean_dec_ref(v___x_4865_);
        if lean_obj_tag(v_fst_4866_) == 0 {
            return v___x_4861_;
        } else {
            let mut v_val_4867_: *mut LeanObject = core::ptr::null_mut();
            v_val_4867_ = lean_ctor_get(v_fst_4866_, 0);
            lean_inc(v_val_4867_);
            lean_dec_ref_known(v_fst_4866_, 1);
            return v_val_4867_;
        }
    } else {
        let mut v_vs_4868_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4871_: usize = 0;
        let mut v___x_4872_: usize = 0;
        let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4874_: *mut LeanObject = core::ptr::null_mut();
        v_vs_4868_ = lean_ctor_get(v_x_4859_, 0);
        v___x_4869_ = lean_box(0);
        v___x_4870_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0;
        v_sz_4871_ = lean_array_size(v_vs_4868_);
        v___x_4872_ = 0usize;
        v___x_4873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(v_p_4858_, v_vs_4868_, v_sz_4871_, v___x_4872_, v___x_4870_);
        v_fst_4874_ = lean_ctor_get(v___x_4873_, 0);
        lean_inc(v_fst_4874_);
        lean_dec_ref(v___x_4873_);
        if lean_obj_tag(v_fst_4874_) == 0 {
            return v___x_4869_;
        } else {
            let mut v_val_4875_: *mut LeanObject = core::ptr::null_mut();
            v_val_4875_ = lean_ctor_get(v_fst_4874_, 0);
            lean_inc(v_val_4875_);
            lean_dec_ref_known(v_fst_4874_, 1);
            return v_val_4875_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0(
    mut v_p_4876_: *mut LeanObject,
    mut v_t_4877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    v_root_4878_ = lean_ctor_get(v_t_4877_, 0);
    v_tail_4879_ = lean_ctor_get(v_t_4877_, 1);
    lean_inc_ref(v_p_4876_);
    v___x_4880_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(v_p_4876_, v_root_4878_);
    if lean_obj_tag(v___x_4880_) == 0 {
        let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4882_: usize = 0;
        let mut v___x_4883_: usize = 0;
        let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4885_: *mut LeanObject = core::ptr::null_mut();
        v___x_4881_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___closed__0;
        v_sz_4882_ = lean_array_size(v_tail_4879_);
        v___x_4883_ = 0usize;
        v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(v_p_4876_, v_tail_4879_, v_sz_4882_, v___x_4883_, v___x_4881_);
        v_fst_4885_ = lean_ctor_get(v___x_4884_, 0);
        lean_inc(v_fst_4885_);
        lean_dec_ref(v___x_4884_);
        if lean_obj_tag(v_fst_4885_) == 0 {
            return v___x_4880_;
        } else {
            let mut v_val_4886_: *mut LeanObject = core::ptr::null_mut();
            v_val_4886_ = lean_ctor_get(v_fst_4885_, 0);
            lean_inc(v_val_4886_);
            lean_dec_ref_known(v_fst_4885_, 1);
            return v_val_4886_;
        }
    } else {
        lean_dec_ref(v_p_4876_);
        return v___x_4880_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_findInfo_x3f(
    mut v_p_4887_: *mut LeanObject,
    mut v_t_4888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_t_4888_) {
                0 => {
                    v_t_4889_ = lean_ctor_get(v_t_4888_, 1);
                    lean_inc_ref(v_t_4889_);
                    lean_dec_ref_known(v_t_4888_, 2);
                    v_t_4888_ = v_t_4889_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_i_4891_ = lean_ctor_get(v_t_4888_, 0);
                    lean_inc_ref_n(v_i_4891_, 2);
                    v_children_4892_ = lean_ctor_get(v_t_4888_, 1);
                    lean_inc_ref(v_children_4892_);
                    lean_dec_ref_known(v_t_4888_, 2);
                    lean_inc_ref(v_p_4887_);
                    v___x_4893_ = lean_apply_1(v_p_4887_, v_i_4891_);
                    v___x_4894_ = (lean_unbox(v___x_4893_) as u8);
                    if v___x_4894_ == 0 {
                        lean_dec_ref(v_i_4891_);
                        v___x_4895_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0(v_p_4887_, v_children_4892_);
                        lean_dec_ref(v_children_4892_);
                        return v___x_4895_;
                    } else {
                        lean_dec_ref(v_children_4892_);
                        lean_dec_ref(v_p_4887_);
                        v___x_4896_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4896_, 0, v_i_4891_);
                        return v___x_4896_;
                    }
                }
                _ => {
                    lean_dec_ref(v_t_4888_);
                    lean_dec_ref(v_p_4887_);
                    v___x_4897_ = lean_box(0);
                    return v___x_4897_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0___boxed(
    mut v_p_4898_: *mut LeanObject,
    mut v_t_4899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4900_: *mut LeanObject = core::ptr::null_mut();
    v_res_4900_ =
        l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0(
            v_p_4898_, v_t_4899_,
        );
    lean_dec_ref(v_t_4899_);
    return v_res_4900_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1___boxed(
    mut v_p_4901_: *mut LeanObject,
    mut v_as_4902_: *mut LeanObject,
    mut v_sz_4903_: *mut LeanObject,
    mut v_i_4904_: *mut LeanObject,
    mut v_b_4905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4906_: usize = 0;
    let mut v_i_boxed_4907_: usize = 0;
    let mut v_res_4908_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4906_ = lean_unbox_usize(v_sz_4903_);
    lean_dec(v_sz_4903_);
    v_i_boxed_4907_ = lean_unbox_usize(v_i_4904_);
    lean_dec(v_i_4904_);
    v_res_4908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__1(v_p_4901_, v_as_4902_, v_sz_boxed_4906_, v_i_boxed_4907_, v_b_4905_);
    lean_dec_ref(v_b_4905_);
    lean_dec_ref(v_as_4902_);
    return v_res_4908_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_p_4909_: *mut LeanObject,
    mut v_as_4910_: *mut LeanObject,
    mut v_sz_4911_: *mut LeanObject,
    mut v_i_4912_: *mut LeanObject,
    mut v_b_4913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4914_: usize = 0;
    let mut v_i_boxed_4915_: usize = 0;
    let mut v_res_4916_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4914_ = lean_unbox_usize(v_sz_4911_);
    lean_dec(v_sz_4911_);
    v_i_boxed_4915_ = lean_unbox_usize(v_i_4912_);
    lean_dec(v_i_4912_);
    v_res_4916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0_spec__1(v_p_4909_, v_as_4910_, v_sz_boxed_4914_, v_i_boxed_4915_, v_b_4913_);
    lean_dec_ref(v_b_4913_);
    lean_dec_ref(v_as_4910_);
    return v_res_4916_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0___boxed(
    mut v_p_4917_: *mut LeanObject,
    mut v_x_4918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4919_: *mut LeanObject = core::ptr::null_mut();
    v_res_4919_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_InfoTree_findInfo_x3f_spec__0_spec__0(v_p_4917_, v_x_4918_);
    lean_dec_ref(v_x_4918_);
    return v_res_4919_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(
    mut v_keys_4920_: *mut LeanObject,
    mut v_vals_4921_: *mut LeanObject,
    mut v_i_4922_: *mut LeanObject,
    mut v_k_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: u8 = 0;
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: u8 = 0;
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4924_ = lean_array_get_size(v_keys_4920_);
                v___x_4925_ = lean_nat_dec_lt(v_i_4922_, v___x_4924_);
                if v___x_4925_ == 0 {
                    lean_dec(v_i_4922_);
                    v___x_4926_ = lean_box(0);
                    return v___x_4926_;
                } else {
                    v_k_x27_4927_ = lean_array_fget_borrowed(v_keys_4920_, v_i_4922_);
                    v___x_4928_ = l_Lean_instBEqMVarId_beq(v_k_4923_, v_k_x27_4927_);
                    if v___x_4928_ == 0 {
                        v___x_4929_ = lean_unsigned_to_nat(1);
                        v___x_4930_ = lean_nat_add(v_i_4922_, v___x_4929_);
                        lean_dec(v_i_4922_);
                        v_i_4922_ = v___x_4930_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4932_ = lean_array_fget_borrowed(v_vals_4921_, v_i_4922_);
                        lean_dec(v_i_4922_);
                        lean_inc(v___x_4932_);
                        v___x_4933_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4933_, 0, v___x_4932_);
                        return v___x_4933_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_keys_4934_: *mut LeanObject,
    mut v_vals_4935_: *mut LeanObject,
    mut v_i_4936_: *mut LeanObject,
    mut v_k_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4938_: *mut LeanObject = core::ptr::null_mut();
    v_res_4938_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_keys_4934_, v_vals_4935_, v_i_4936_, v_k_4937_);
    lean_dec(v_k_4937_);
    lean_dec_ref(v_vals_4935_);
    lean_dec_ref(v_keys_4934_);
    return v_res_4938_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_4939_: usize = 0;
    let mut v___x_4940_: usize = 0;
    let mut v___x_4941_: usize = 0;
    v___x_4939_ = 5usize;
    v___x_4940_ = 1usize;
    v___x_4941_ = lean_usize_shift_left(v___x_4940_, v___x_4939_);
    return v___x_4941_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_4942_: usize = 0;
    let mut v___x_4943_: usize = 0;
    let mut v___x_4944_: usize = 0;
    v___x_4942_ = 1usize;
    v___x_4943_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__0);
    v___x_4944_ = lean_usize_sub(v___x_4943_, v___x_4942_);
    return v___x_4944_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(
    mut v_x_4945_: *mut LeanObject,
    mut v_x_4946_: usize,
    mut v_x_4947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: usize = 0;
    let mut v___x_4951_: usize = 0;
    let mut v___x_4952_: usize = 0;
    let mut v_j_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: u8 = 0;
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: usize = 0;
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4945_) == 0 {
                    v_es_4948_ = lean_ctor_get(v_x_4945_, 0);
                    v___x_4949_ = lean_box(2);
                    v___x_4950_ = 5usize;
                    v___x_4951_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___closed__1);
                    v___x_4952_ = lean_usize_land(v_x_4946_, v___x_4951_);
                    v_j_4953_ = lean_usize_to_nat(v___x_4952_);
                    v___x_4954_ = lean_array_get_borrowed(v___x_4949_, v_es_4948_, v_j_4953_);
                    lean_dec(v_j_4953_);
                    match lean_obj_tag(v___x_4954_) {
                        0 => {
                            v_key_4955_ = lean_ctor_get(v___x_4954_, 0);
                            v_val_4956_ = lean_ctor_get(v___x_4954_, 1);
                            v___x_4957_ = l_Lean_instBEqMVarId_beq(v_x_4947_, v_key_4955_);
                            if v___x_4957_ == 0 {
                                v___x_4958_ = lean_box(0);
                                return v___x_4958_;
                            } else {
                                lean_inc(v_val_4956_);
                                v___x_4959_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4959_, 0, v_val_4956_);
                                return v___x_4959_;
                            }
                        }
                        1 => {
                            v_node_4960_ = lean_ctor_get(v___x_4954_, 0);
                            v___x_4961_ = lean_usize_shift_right(v_x_4946_, v___x_4950_);
                            v_x_4945_ = v_node_4960_;
                            v_x_4946_ = v___x_4961_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4963_ = lean_box(0);
                            return v___x_4963_;
                        }
                    }
                } else {
                    v_ks_4964_ = lean_ctor_get(v_x_4945_, 0);
                    v_vs_4965_ = lean_ctor_get(v_x_4945_, 1);
                    v___x_4966_ = lean_unsigned_to_nat(0);
                    v___x_4967_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_ks_4964_, v_vs_4965_, v___x_4966_, v_x_4947_);
                    return v___x_4967_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg___boxed(
    mut v_x_4968_: *mut LeanObject,
    mut v_x_4969_: *mut LeanObject,
    mut v_x_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_693__boxed_4971_: usize = 0;
    let mut v_res_4972_: *mut LeanObject = core::ptr::null_mut();
    v_x_693__boxed_4971_ = lean_unbox_usize(v_x_4969_);
    lean_dec(v_x_4969_);
    v_res_4972_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_4968_, v_x_693__boxed_4971_, v_x_4970_);
    lean_dec(v_x_4970_);
    lean_dec_ref(v_x_4968_);
    return v_res_4972_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(
    mut v_x_4973_: *mut LeanObject,
    mut v_x_4974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4975_: u64 = 0;
    let mut v___x_4976_: usize = 0;
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    v___x_4975_ = l_Lean_instHashableMVarId_hash(v_x_4974_);
    v___x_4976_ = lean_uint64_to_usize(v___x_4975_);
    v___x_4977_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_4973_, v___x_4976_, v_x_4974_);
    return v___x_4977_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg___boxed(
    mut v_x_4978_: *mut LeanObject,
    mut v_x_4979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4980_: *mut LeanObject = core::ptr::null_mut();
    v_res_4980_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(
            v_x_4978_, v_x_4979_,
        );
    lean_dec(v_x_4979_);
    lean_dec_ref(v_x_4978_);
    return v_res_4980_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(
    mut v_assignment_4981_: *mut LeanObject,
    mut v_sz_4982_: usize,
    mut v_i_4983_: usize,
    mut v_bs_4984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4985_: u8 = 0;
    let mut v_v_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: usize = 0;
    let mut v___x_4991_: usize = 0;
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4985_ = lean_usize_dec_lt(v_i_4983_, v_sz_4982_);
                if v___x_4985_ == 0 {
                    return v_bs_4984_;
                } else {
                    v_v_4986_ = lean_array_uget(v_bs_4984_, v_i_4983_);
                    v___x_4987_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4988_ = lean_array_uset(v_bs_4984_, v_i_4983_, v___x_4987_);
                    v___x_4989_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_4981_, v_v_4986_);
                    v___x_4990_ = 1usize;
                    v___x_4991_ = lean_usize_add(v_i_4983_, v___x_4990_);
                    v___x_4992_ = lean_array_uset(v_bs_x27_4988_, v_i_4983_, v___x_4989_);
                    v_i_4983_ = v___x_4991_;
                    v_bs_4984_ = v___x_4992_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_substitute(
    mut v_tree_4994_: *mut LeanObject,
    mut v_assignment_4995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5000_: u8 = 0;
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5005_: u8 = 0;
    let mut v_i_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5010_: u8 = 0;
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_mvarId_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_tree_4994_) {
                0 => {
                    v_i_4996_ = lean_ctor_get(v_tree_4994_, 0);
                    v_t_4997_ = lean_ctor_get(v_tree_4994_, 1);
                    v_isSharedCheck_5005_ = (!lean_is_exclusive(v_tree_4994_)) as u8;
                    if v_isSharedCheck_5005_ == 0 {
                        v___x_4999_ = v_tree_4994_;
                        v_isShared_5000_ = v_isSharedCheck_5005_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_t_4997_);
                        lean_inc(v_i_4996_);
                        lean_dec(v_tree_4994_);
                        v___x_4999_ = lean_box(0);
                        v_isShared_5000_ = v_isSharedCheck_5005_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_5006_ = lean_ctor_get(v_tree_4994_, 0);
                    v_children_5007_ = lean_ctor_get(v_tree_4994_, 1);
                    v_isSharedCheck_5015_ = (!lean_is_exclusive(v_tree_4994_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_5009_ = v_tree_4994_;
                        v_isShared_5010_ = v_isSharedCheck_5015_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_children_5007_);
                        lean_inc(v_i_5006_);
                        lean_dec(v_tree_4994_);
                        v___x_5009_ = lean_box(0);
                        v_isShared_5010_ = v_isSharedCheck_5015_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_mvarId_5016_ = lean_ctor_get(v_tree_4994_, 0);
                    v___x_5017_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(v_assignment_4995_, v_mvarId_5016_);
                    if lean_obj_tag(v___x_5017_) == 0 {
                        return v_tree_4994_;
                    } else {
                        lean_dec_ref_known(v_tree_4994_, 1);
                        v_val_5018_ = lean_ctor_get(v___x_5017_, 0);
                        lean_inc(v_val_5018_);
                        lean_dec_ref_known(v___x_5017_, 1);
                        v_tree_4994_ = v_val_5018_;
                        state = 0;
                        continue;
                    }
                }
            },
            1 => {
                v___x_5001_ = l_Lean_Elab_InfoTree_substitute(v_t_4997_, v_assignment_4995_);
                if v_isShared_5000_ == 0 {
                    lean_ctor_set(v___x_4999_, 1, v___x_5001_);
                    v___x_5003_ = v___x_4999_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_i_4996_);
                    lean_ctor_set(v_reuseFailAlloc_5004_, 1, v___x_5001_);
                    v___x_5003_ = v_reuseFailAlloc_5004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5003_;
            }
            3 => {
                v___x_5011_ =
                    l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(
                        v_assignment_4995_,
                        v_children_5007_,
                    );
                if v_isShared_5010_ == 0 {
                    lean_ctor_set(v___x_5009_, 1, v___x_5011_);
                    v___x_5013_ = v___x_5009_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_i_5006_);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 1, v___x_5011_);
                    v___x_5013_ = v_reuseFailAlloc_5014_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(
    mut v_assignment_5020_: *mut LeanObject,
    mut v_sz_5021_: usize,
    mut v_i_5022_: usize,
    mut v_bs_5023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5024_: u8 = 0;
    let mut v_v_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: usize = 0;
    let mut v___x_5030_: usize = 0;
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5024_ = lean_usize_dec_lt(v_i_5022_, v_sz_5021_);
                if v___x_5024_ == 0 {
                    return v_bs_5023_;
                } else {
                    v_v_5025_ = lean_array_uget(v_bs_5023_, v_i_5022_);
                    v___x_5026_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5027_ = lean_array_uset(v_bs_5023_, v_i_5022_, v___x_5026_);
                    v___x_5028_ = l_Lean_Elab_InfoTree_substitute(v_v_5025_, v_assignment_5020_);
                    v___x_5029_ = 1usize;
                    v___x_5030_ = lean_usize_add(v_i_5022_, v___x_5029_);
                    v___x_5031_ = lean_array_uset(v_bs_x27_5027_, v_i_5022_, v___x_5028_);
                    v_i_5022_ = v___x_5030_;
                    v_bs_5023_ = v___x_5031_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(
    mut v_assignment_5033_: *mut LeanObject,
    mut v_x_5034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v_sz_5039_: usize = 0;
    let mut v___x_5040_: usize = 0;
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut v_vs_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v_sz_5050_: usize = 0;
    let mut v___x_5051_: usize = 0;
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5034_) == 0 {
                    v_cs_5035_ = lean_ctor_get(v_x_5034_, 0);
                    v_isSharedCheck_5045_ = (!lean_is_exclusive(v_x_5034_)) as u8;
                    if v_isSharedCheck_5045_ == 0 {
                        v___x_5037_ = v_x_5034_;
                        v_isShared_5038_ = v_isSharedCheck_5045_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_5035_);
                        lean_dec(v_x_5034_);
                        v___x_5037_ = lean_box(0);
                        v_isShared_5038_ = v_isSharedCheck_5045_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5046_ = lean_ctor_get(v_x_5034_, 0);
                    v_isSharedCheck_5056_ = (!lean_is_exclusive(v_x_5034_)) as u8;
                    if v_isSharedCheck_5056_ == 0 {
                        v___x_5048_ = v_x_5034_;
                        v_isShared_5049_ = v_isSharedCheck_5056_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_vs_5046_);
                        lean_dec(v_x_5034_);
                        v___x_5048_ = lean_box(0);
                        v_isShared_5049_ = v_isSharedCheck_5056_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5039_ = lean_array_size(v_cs_5035_);
                v___x_5040_ = 0usize;
                v___x_5041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(v_assignment_5033_, v_sz_5039_, v___x_5040_, v_cs_5035_);
                if v_isShared_5038_ == 0 {
                    lean_ctor_set(v___x_5037_, 0, v___x_5041_);
                    v___x_5043_ = v___x_5037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5041_);
                    v___x_5043_ = v_reuseFailAlloc_5044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5043_;
            }
            3 => {
                v_sz_5050_ = lean_array_size(v_vs_5046_);
                v___x_5051_ = 0usize;
                v___x_5052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_5033_, v_sz_5050_, v___x_5051_, v_vs_5046_);
                if v_isShared_5049_ == 0 {
                    lean_ctor_set(v___x_5048_, 0, v___x_5052_);
                    v___x_5054_ = v___x_5048_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5052_);
                    v___x_5054_ = v_reuseFailAlloc_5055_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(
    mut v_assignment_5057_: *mut LeanObject,
    mut v_t_5058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_5062_: usize = 0;
    let mut v_tailOff_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5066_: u8 = 0;
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5068_: usize = 0;
    let mut v___x_5069_: usize = 0;
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5059_ = lean_ctor_get(v_t_5058_, 0);
                v_tail_5060_ = lean_ctor_get(v_t_5058_, 1);
                v_size_5061_ = lean_ctor_get(v_t_5058_, 2);
                v_shift_5062_ = lean_ctor_get_usize(v_t_5058_, 4);
                v_tailOff_5063_ = lean_ctor_get(v_t_5058_, 3);
                v_isSharedCheck_5074_ = (!lean_is_exclusive(v_t_5058_)) as u8;
                if v_isSharedCheck_5074_ == 0 {
                    v___x_5065_ = v_t_5058_;
                    v_isShared_5066_ = v_isSharedCheck_5074_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_5063_);
                    lean_inc(v_size_5061_);
                    lean_inc(v_tail_5060_);
                    lean_inc(v_root_5059_);
                    lean_dec(v_t_5058_);
                    v___x_5065_ = lean_box(0);
                    v_isShared_5066_ = v_isSharedCheck_5074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5067_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_5057_, v_root_5059_);
                v_sz_5068_ = lean_array_size(v_tail_5060_);
                v___x_5069_ = 0usize;
                v___x_5070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_5057_, v_sz_5068_, v___x_5069_, v_tail_5060_);
                if v_isShared_5066_ == 0 {
                    lean_ctor_set(v___x_5065_, 1, v___x_5070_);
                    lean_ctor_set(v___x_5065_, 0, v___x_5067_);
                    v___x_5072_ = v___x_5065_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5073_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5067_);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 1, v___x_5070_);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 2, v_size_5061_);
                    lean_ctor_set(v_reuseFailAlloc_5073_, 3, v_tailOff_5063_);
                    lean_ctor_set_usize(v_reuseFailAlloc_5073_, 4, v_shift_5062_);
                    v___x_5072_ = v_reuseFailAlloc_5073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0___boxed(
    mut v_assignment_5075_: *mut LeanObject,
    mut v_t_5076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5077_: *mut LeanObject = core::ptr::null_mut();
    v_res_5077_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0(
        v_assignment_5075_,
        v_t_5076_,
    );
    lean_dec_ref(v_assignment_5075_);
    return v_res_5077_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0___boxed(
    mut v_assignment_5078_: *mut LeanObject,
    mut v_x_5079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5080_: *mut LeanObject = core::ptr::null_mut();
    v_res_5080_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0(v_assignment_5078_, v_x_5079_);
    lean_dec_ref(v_assignment_5078_);
    return v_res_5080_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1___boxed(
    mut v_assignment_5081_: *mut LeanObject,
    mut v_sz_5082_: *mut LeanObject,
    mut v_i_5083_: *mut LeanObject,
    mut v_bs_5084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5085_: usize = 0;
    let mut v_i_boxed_5086_: usize = 0;
    let mut v_res_5087_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5085_ = lean_unbox_usize(v_sz_5082_);
    lean_dec(v_sz_5082_);
    v_i_boxed_5086_ = lean_unbox_usize(v_i_5083_);
    lean_dec(v_i_5083_);
    v_res_5087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__1(v_assignment_5081_, v_sz_boxed_5085_, v_i_boxed_5086_, v_bs_5084_);
    lean_dec_ref(v_assignment_5081_);
    return v_res_5087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1___boxed(
    mut v_assignment_5088_: *mut LeanObject,
    mut v_sz_5089_: *mut LeanObject,
    mut v_i_5090_: *mut LeanObject,
    mut v_bs_5091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5092_: usize = 0;
    let mut v_i_boxed_5093_: usize = 0;
    let mut v_res_5094_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5092_ = lean_unbox_usize(v_sz_5089_);
    lean_dec(v_sz_5089_);
    v_i_boxed_5093_ = lean_unbox_usize(v_i_5090_);
    lean_dec(v_i_5090_);
    v_res_5094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoTree_substitute_spec__0_spec__0_spec__1(v_assignment_5088_, v_sz_boxed_5092_, v_i_boxed_5093_, v_bs_5091_);
    lean_dec_ref(v_assignment_5088_);
    return v_res_5094_;
}
pub unsafe fn l_Lean_Elab_InfoTree_substitute___boxed(
    mut v_tree_5095_: *mut LeanObject,
    mut v_assignment_5096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5097_: *mut LeanObject = core::ptr::null_mut();
    v_res_5097_ = l_Lean_Elab_InfoTree_substitute(v_tree_5095_, v_assignment_5096_);
    lean_dec_ref(v_assignment_5096_);
    return v_res_5097_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(
    mut v_00_u03b2_5098_: *mut LeanObject,
    mut v_x_5099_: *mut LeanObject,
    mut v_x_5100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    v___x_5101_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___redArg(
            v_x_5099_, v_x_5100_,
        );
    return v___x_5101_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1___boxed(
    mut v_00_u03b2_5102_: *mut LeanObject,
    mut v_x_5103_: *mut LeanObject,
    mut v_x_5104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5105_: *mut LeanObject = core::ptr::null_mut();
    v_res_5105_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1(
        v_00_u03b2_5102_,
        v_x_5103_,
        v_x_5104_,
    );
    lean_dec(v_x_5104_);
    lean_dec_ref(v_x_5103_);
    return v_res_5105_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(
    mut v_00_u03b2_5106_: *mut LeanObject,
    mut v_x_5107_: *mut LeanObject,
    mut v_x_5108_: usize,
    mut v_x_5109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    v___x_5110_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___redArg(v_x_5107_, v_x_5108_, v_x_5109_);
    return v___x_5110_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3___boxed(
    mut v_00_u03b2_5111_: *mut LeanObject,
    mut v_x_5112_: *mut LeanObject,
    mut v_x_5113_: *mut LeanObject,
    mut v_x_5114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_905__boxed_5115_: usize = 0;
    let mut v_res_5116_: *mut LeanObject = core::ptr::null_mut();
    v_x_905__boxed_5115_ = lean_unbox_usize(v_x_5113_);
    lean_dec(v_x_5113_);
    v_res_5116_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3(v_00_u03b2_5111_, v_x_5112_, v_x_905__boxed_5115_, v_x_5114_);
    lean_dec(v_x_5114_);
    lean_dec_ref(v_x_5112_);
    return v_res_5116_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(
    mut v_00_u03b2_5117_: *mut LeanObject,
    mut v_keys_5118_: *mut LeanObject,
    mut v_vals_5119_: *mut LeanObject,
    mut v_heq_5120_: *mut LeanObject,
    mut v_i_5121_: *mut LeanObject,
    mut v_k_5122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    v___x_5123_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___redArg(v_keys_5118_, v_vals_5119_, v_i_5121_, v_k_5122_);
    return v___x_5123_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b2_5124_: *mut LeanObject,
    mut v_keys_5125_: *mut LeanObject,
    mut v_vals_5126_: *mut LeanObject,
    mut v_heq_5127_: *mut LeanObject,
    mut v_i_5128_: *mut LeanObject,
    mut v_k_5129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5130_: *mut LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_InfoTree_substitute_spec__1_spec__3_spec__5(v_00_u03b2_5124_, v_keys_5125_, v_vals_5126_, v_heq_5127_, v_i_5128_, v_k_5129_);
    lean_dec(v_k_5129_);
    lean_dec_ref(v_vals_5126_);
    lean_dec_ref(v_keys_5125_);
    return v_res_5130_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(
    mut v_f_5131_: *mut LeanObject,
    mut v_as_5132_: *mut LeanObject,
    mut v_i_5133_: *mut LeanObject,
    mut v_acc_5134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: u8 = 0;
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5135_ = lean_array_get_size(v_as_5132_);
                v___x_5136_ = lean_nat_dec_eq(v_i_5133_, v___x_5135_);
                if v___x_5136_ == 0 {
                    v___x_5137_ = lean_array_fget_borrowed(v_as_5132_, v_i_5133_);
                    lean_inc(v_f_5131_);
                    lean_inc(v___x_5137_);
                    v___x_5138_ = lean_apply_1(v_f_5131_, v___x_5137_);
                    v___x_5139_ = lean_unsigned_to_nat(1);
                    v___x_5140_ = lean_nat_add(v_i_5133_, v___x_5139_);
                    lean_dec(v_i_5133_);
                    v___x_5141_ = lean_array_push(v_acc_5134_, v___x_5138_);
                    v_i_5133_ = v___x_5140_;
                    v_acc_5134_ = v___x_5141_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_i_5133_);
                    lean_dec(v_f_5131_);
                    return v_acc_5134_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg___boxed(
    mut v_f_5143_: *mut LeanObject,
    mut v_as_5144_: *mut LeanObject,
    mut v_i_5145_: *mut LeanObject,
    mut v_acc_5146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5147_: *mut LeanObject = core::ptr::null_mut();
    v_res_5147_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_5143_, v_as_5144_, v_i_5145_, v_acc_5146_);
    lean_dec_ref(v_as_5144_);
    return v_res_5147_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_f_5148_: *mut LeanObject,
    mut v_as_5149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    v___x_5150_ = lean_unsigned_to_nat(0);
    v___x_5151_ = lean_array_get_size(v_as_5149_);
    v___x_5152_ = lean_mk_empty_array_with_capacity(v___x_5151_);
    v___x_5153_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_5148_, v_as_5149_, v___x_5150_, v___x_5152_);
    return v___x_5153_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_f_5154_: *mut LeanObject,
    mut v_as_5155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5156_: *mut LeanObject = core::ptr::null_mut();
    v_res_5156_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_5154_, v_as_5155_);
    lean_dec_ref(v_as_5155_);
    return v_res_5156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_f_5157_: *mut LeanObject,
    mut v_sz_5158_: usize,
    mut v_i_5159_: usize,
    mut v_bs_5160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5161_: u8 = 0;
    let mut v_v_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: usize = 0;
    let mut v___x_5168_: usize = 0;
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5175_: u8 = 0;
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_node_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5189_: u8 = 0;
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5161_ = lean_usize_dec_lt(v_i_5159_, v_sz_5158_);
                if v___x_5161_ == 0 {
                    lean_dec(v_f_5157_);
                    return v_bs_5160_;
                } else {
                    v_v_5162_ = lean_array_uget(v_bs_5160_, v_i_5159_);
                    v___x_5163_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5164_ = lean_array_uset(v_bs_5160_, v_i_5159_, v___x_5163_);
                    match lean_obj_tag(v_v_5162_) {
                        0 => {
                            v_key_5171_ = lean_ctor_get(v_v_5162_, 0);
                            v_val_5172_ = lean_ctor_get(v_v_5162_, 1);
                            v_isSharedCheck_5180_ = (!lean_is_exclusive(v_v_5162_)) as u8;
                            if v_isSharedCheck_5180_ == 0 {
                                v___x_5174_ = v_v_5162_;
                                v_isShared_5175_ = v_isSharedCheck_5180_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_5172_);
                                lean_inc(v_key_5171_);
                                lean_dec(v_v_5162_);
                                v___x_5174_ = lean_box(0);
                                v_isShared_5175_ = v_isSharedCheck_5180_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            v_node_5181_ = lean_ctor_get(v_v_5162_, 0);
                            v_isSharedCheck_5189_ = (!lean_is_exclusive(v_v_5162_)) as u8;
                            if v_isSharedCheck_5189_ == 0 {
                                v___x_5183_ = v_v_5162_;
                                v_isShared_5184_ = v_isSharedCheck_5189_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_node_5181_);
                                lean_dec(v_v_5162_);
                                v___x_5183_ = lean_box(0);
                                v_isShared_5184_ = v_isSharedCheck_5189_;
                                state = 4;
                                continue;
                            }
                        }
                        _ => {
                            v___x_5190_ = lean_box(2);
                            v___y_5166_ = v___x_5190_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5167_ = 1usize;
                v___x_5168_ = lean_usize_add(v_i_5159_, v___x_5167_);
                v___x_5169_ = lean_array_uset(v_bs_x27_5164_, v_i_5159_, v___y_5166_);
                v_i_5159_ = v___x_5168_;
                v_bs_5160_ = v___x_5169_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v_f_5157_);
                v___x_5176_ = lean_apply_1(v_f_5157_, v_val_5172_);
                if v_isShared_5175_ == 0 {
                    lean_ctor_set(v___x_5174_, 1, v___x_5176_);
                    v___x_5178_ = v___x_5174_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_key_5171_);
                    lean_ctor_set(v_reuseFailAlloc_5179_, 1, v___x_5176_);
                    v___x_5178_ = v_reuseFailAlloc_5179_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5166_ = v___x_5178_;
                state = 1;
                continue;
            }
            4 => {
                lean_inc(v_f_5157_);
                v___x_5185_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_5157_, v_node_5181_);
                if v_isShared_5184_ == 0 {
                    lean_ctor_set(v___x_5183_, 0, v___x_5185_);
                    v___x_5187_ = v___x_5183_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
                    v___x_5187_ = v_reuseFailAlloc_5188_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5166_ = v___x_5187_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(
    mut v_f_5191_: *mut LeanObject,
    mut v_n_5192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5196_: u8 = 0;
    let mut v_sz_5197_: usize = 0;
    let mut v___x_5198_: usize = 0;
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5203_: u8 = 0;
    let mut v_ks_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5208_: u8 = 0;
    let mut v_val_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5192_) == 0 {
                    v_es_5193_ = lean_ctor_get(v_n_5192_, 0);
                    v_isSharedCheck_5203_ = (!lean_is_exclusive(v_n_5192_)) as u8;
                    if v_isSharedCheck_5203_ == 0 {
                        v___x_5195_ = v_n_5192_;
                        v_isShared_5196_ = v_isSharedCheck_5203_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_5193_);
                        lean_dec(v_n_5192_);
                        v___x_5195_ = lean_box(0);
                        v_isShared_5196_ = v_isSharedCheck_5203_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_5204_ = lean_ctor_get(v_n_5192_, 0);
                    v_vs_5205_ = lean_ctor_get(v_n_5192_, 1);
                    v_isSharedCheck_5213_ = (!lean_is_exclusive(v_n_5192_)) as u8;
                    if v_isSharedCheck_5213_ == 0 {
                        v___x_5207_ = v_n_5192_;
                        v_isShared_5208_ = v_isSharedCheck_5213_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_vs_5205_);
                        lean_inc(v_ks_5204_);
                        lean_dec(v_n_5192_);
                        v___x_5207_ = lean_box(0);
                        v_isShared_5208_ = v_isSharedCheck_5213_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5197_ = lean_array_size(v_es_5193_);
                v___x_5198_ = 0usize;
                v___x_5199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_5191_, v_sz_5197_, v___x_5198_, v_es_5193_);
                if v_isShared_5196_ == 0 {
                    lean_ctor_set(v___x_5195_, 0, v___x_5199_);
                    v___x_5201_ = v___x_5195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5199_);
                    v___x_5201_ = v_reuseFailAlloc_5202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5201_;
            }
            3 => {
                v_val_5209_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_5191_, v_vs_5205_);
                lean_dec_ref(v_vs_5205_);
                if v_isShared_5208_ == 0 {
                    lean_ctor_set(v___x_5207_, 1, v_val_5209_);
                    v___x_5211_ = v___x_5207_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_ks_5204_);
                    lean_ctor_set(v_reuseFailAlloc_5212_, 1, v_val_5209_);
                    v___x_5211_ = v_reuseFailAlloc_5212_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_f_5214_: *mut LeanObject,
    mut v_sz_5215_: *mut LeanObject,
    mut v_i_5216_: *mut LeanObject,
    mut v_bs_5217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5218_: usize = 0;
    let mut v_i_boxed_5219_: usize = 0;
    let mut v_res_5220_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5218_ = lean_unbox_usize(v_sz_5215_);
    lean_dec(v_sz_5215_);
    v_i_boxed_5219_ = lean_unbox_usize(v_i_5216_);
    lean_dec(v_i_5216_);
    v_res_5220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_5214_, v_sz_boxed_5218_, v_i_boxed_5219_, v_bs_5217_);
    return v_res_5220_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0(
    mut v_f_5221_: *mut LeanObject,
    mut v_x_5222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    v___x_5223_ = lean_apply_1(v_f_5221_, v_x_5222_);
    return v___x_5223_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(
    mut v_pm_5224_: *mut LeanObject,
    mut v_f_5225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    v___f_5226_ = lean_alloc_closure(l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_5226_, 0, v_f_5225_);
    v___x_5227_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v___f_5226_, v_pm_5224_);
    return v___x_5227_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___lam__0(
    mut v_x_5228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    v___x_5229_ = lean_task_get_own(v_x_5228_);
    return v___x_5229_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(
    mut v_s_5231_: *mut LeanObject,
    mut v_sz_5232_: usize,
    mut v_i_5233_: usize,
    mut v_bs_5234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5235_: u8 = 0;
    let mut v_lazyAssignment_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: usize = 0;
    let mut v___x_5244_: usize = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = lean_usize_dec_lt(v_i_5233_, v_sz_5232_);
                if v___x_5235_ == 0 {
                    lean_dec_ref(v_s_5231_);
                    return v_bs_5234_;
                } else {
                    v_lazyAssignment_5236_ = lean_ctor_get(v_s_5231_, 1);
                    v_v_5237_ = lean_array_uget(v_bs_5234_, v_i_5233_);
                    v___f_5238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___closed__0;
                    v___x_5239_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5240_ = lean_array_uset(v_bs_5234_, v_i_5233_, v___x_5239_);
                    lean_inc_ref(v_lazyAssignment_5236_);
                    v___x_5241_ = l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(v_lazyAssignment_5236_, v___f_5238_);
                    v___x_5242_ = l_Lean_Elab_InfoTree_substitute(v_v_5237_, v___x_5241_);
                    lean_dec_ref(v___x_5241_);
                    v___x_5243_ = 1usize;
                    v___x_5244_ = lean_usize_add(v_i_5233_, v___x_5243_);
                    v___x_5245_ = lean_array_uset(v_bs_x27_5240_, v_i_5233_, v___x_5242_);
                    v_i_5233_ = v___x_5244_;
                    v_bs_5234_ = v___x_5245_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3___boxed(
    mut v_s_5247_: *mut LeanObject,
    mut v_sz_5248_: *mut LeanObject,
    mut v_i_5249_: *mut LeanObject,
    mut v_bs_5250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5251_: usize = 0;
    let mut v_i_boxed_5252_: usize = 0;
    let mut v_res_5253_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5251_ = lean_unbox_usize(v_sz_5248_);
    lean_dec(v_sz_5248_);
    v_i_boxed_5252_ = lean_unbox_usize(v_i_5249_);
    lean_dec(v_i_5249_);
    v_res_5253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_5247_, v_sz_boxed_5251_, v_i_boxed_5252_, v_bs_5250_);
    return v_res_5253_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(
    mut v_s_5254_: *mut LeanObject,
    mut v_sz_5255_: usize,
    mut v_i_5256_: usize,
    mut v_bs_5257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5258_: u8 = 0;
    let mut v_v_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: usize = 0;
    let mut v___x_5264_: usize = 0;
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5258_ = lean_usize_dec_lt(v_i_5256_, v_sz_5255_);
                if v___x_5258_ == 0 {
                    lean_dec_ref(v_s_5254_);
                    return v_bs_5257_;
                } else {
                    v_v_5259_ = lean_array_uget(v_bs_5257_, v_i_5256_);
                    v___x_5260_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5261_ = lean_array_uset(v_bs_5257_, v_i_5256_, v___x_5260_);
                    lean_inc_ref(v_s_5254_);
                    v___x_5262_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_5254_, v_v_5259_);
                    v___x_5263_ = 1usize;
                    v___x_5264_ = lean_usize_add(v_i_5256_, v___x_5263_);
                    v___x_5265_ = lean_array_uset(v_bs_x27_5261_, v_i_5256_, v___x_5262_);
                    v_i_5256_ = v___x_5264_;
                    v_bs_5257_ = v___x_5265_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(
    mut v_s_5267_: *mut LeanObject,
    mut v_x_5268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5272_: u8 = 0;
    let mut v_sz_5273_: usize = 0;
    let mut v___x_5274_: usize = 0;
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5279_: u8 = 0;
    let mut v_vs_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5283_: u8 = 0;
    let mut v_sz_5284_: usize = 0;
    let mut v___x_5285_: usize = 0;
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5268_) == 0 {
                    v_cs_5269_ = lean_ctor_get(v_x_5268_, 0);
                    v_isSharedCheck_5279_ = (!lean_is_exclusive(v_x_5268_)) as u8;
                    if v_isSharedCheck_5279_ == 0 {
                        v___x_5271_ = v_x_5268_;
                        v_isShared_5272_ = v_isSharedCheck_5279_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_5269_);
                        lean_dec(v_x_5268_);
                        v___x_5271_ = lean_box(0);
                        v_isShared_5272_ = v_isSharedCheck_5279_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5280_ = lean_ctor_get(v_x_5268_, 0);
                    v_isSharedCheck_5290_ = (!lean_is_exclusive(v_x_5268_)) as u8;
                    if v_isSharedCheck_5290_ == 0 {
                        v___x_5282_ = v_x_5268_;
                        v_isShared_5283_ = v_isSharedCheck_5290_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_vs_5280_);
                        lean_dec(v_x_5268_);
                        v___x_5282_ = lean_box(0);
                        v_isShared_5283_ = v_isSharedCheck_5290_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5273_ = lean_array_size(v_cs_5269_);
                v___x_5274_ = 0usize;
                v___x_5275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_5267_, v_sz_5273_, v___x_5274_, v_cs_5269_);
                if v_isShared_5272_ == 0 {
                    lean_ctor_set(v___x_5271_, 0, v___x_5275_);
                    v___x_5277_ = v___x_5271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5275_);
                    v___x_5277_ = v_reuseFailAlloc_5278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5277_;
            }
            3 => {
                v_sz_5284_ = lean_array_size(v_vs_5280_);
                v___x_5285_ = 0usize;
                v___x_5286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_5267_, v_sz_5284_, v___x_5285_, v_vs_5280_);
                if v_isShared_5283_ == 0 {
                    lean_ctor_set(v___x_5282_, 0, v___x_5286_);
                    v___x_5288_ = v___x_5282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 0, v___x_5286_);
                    v___x_5288_ = v_reuseFailAlloc_5289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4___boxed(
    mut v_s_5291_: *mut LeanObject,
    mut v_sz_5292_: *mut LeanObject,
    mut v_i_5293_: *mut LeanObject,
    mut v_bs_5294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5295_: usize = 0;
    let mut v_i_boxed_5296_: usize = 0;
    let mut v_res_5297_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5295_ = lean_unbox_usize(v_sz_5292_);
    lean_dec(v_sz_5292_);
    v_i_boxed_5296_ = lean_unbox_usize(v_i_5293_);
    lean_dec(v_i_5293_);
    v_res_5297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2_spec__4(v_s_5291_, v_sz_boxed_5295_, v_i_boxed_5296_, v_bs_5294_);
    return v_res_5297_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(
    mut v_s_5298_: *mut LeanObject,
    mut v_t_5299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_5303_: usize = 0;
    let mut v_tailOff_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5307_: u8 = 0;
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5309_: usize = 0;
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5300_ = lean_ctor_get(v_t_5299_, 0);
                v_tail_5301_ = lean_ctor_get(v_t_5299_, 1);
                v_size_5302_ = lean_ctor_get(v_t_5299_, 2);
                v_shift_5303_ = lean_ctor_get_usize(v_t_5299_, 4);
                v_tailOff_5304_ = lean_ctor_get(v_t_5299_, 3);
                v_isSharedCheck_5315_ = (!lean_is_exclusive(v_t_5299_)) as u8;
                if v_isSharedCheck_5315_ == 0 {
                    v___x_5306_ = v_t_5299_;
                    v_isShared_5307_ = v_isSharedCheck_5315_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_5304_);
                    lean_inc(v_size_5302_);
                    lean_inc(v_tail_5301_);
                    lean_inc(v_root_5300_);
                    lean_dec(v_t_5299_);
                    v___x_5306_ = lean_box(0);
                    v_isShared_5307_ = v_isSharedCheck_5315_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_s_5298_);
                v___x_5308_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__2(v_s_5298_, v_root_5300_);
                v_sz_5309_ = lean_array_size(v_tail_5301_);
                v___x_5310_ = 0usize;
                v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1_spec__3(v_s_5298_, v_sz_5309_, v___x_5310_, v_tail_5301_);
                if v_isShared_5307_ == 0 {
                    lean_ctor_set(v___x_5306_, 1, v___x_5311_);
                    lean_ctor_set(v___x_5306_, 0, v___x_5308_);
                    v___x_5313_ = v___x_5306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5308_);
                    lean_ctor_set(v_reuseFailAlloc_5314_, 1, v___x_5311_);
                    lean_ctor_set(v_reuseFailAlloc_5314_, 2, v_size_5302_);
                    lean_ctor_set(v_reuseFailAlloc_5314_, 3, v_tailOff_5304_);
                    lean_ctor_set_usize(v_reuseFailAlloc_5314_, 4, v_shift_5303_);
                    v___x_5313_ = v_reuseFailAlloc_5314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    v___x_5316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5316_;
}
pub unsafe fn _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    v___x_5317_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0_once),
        _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__0,
    );
    v___x_5318_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5318_, 0, v___x_5317_);
    return v___x_5318_;
}
pub unsafe fn l_Lean_Elab_InfoState_substituteLazy___lam__0(
    mut v_s_5319_: *mut LeanObject,
    mut v_trees_5320_: *mut LeanObject,
    mut v_enabled_5321_: u8,
    mut v_assignment_5322_: *mut LeanObject,
    mut v_x_5323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    v___x_5324_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1_once),
        _init_l_Lean_Elab_InfoState_substituteLazy___lam__0___closed__1,
    );
    v___x_5325_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_InfoState_substituteLazy_spec__1(
        v_s_5319_,
        v_trees_5320_,
    );
    v___x_5326_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_5326_, 0, v_assignment_5322_);
    lean_ctor_set(v___x_5326_, 1, v___x_5324_);
    lean_ctor_set(v___x_5326_, 2, v___x_5325_);
    lean_ctor_set_uint8(
        v___x_5326_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_enabled_5321_,
    );
    return v___x_5326_;
}
pub unsafe fn l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed(
    mut v_s_5327_: *mut LeanObject,
    mut v_trees_5328_: *mut LeanObject,
    mut v_enabled_5329_: *mut LeanObject,
    mut v_assignment_5330_: *mut LeanObject,
    mut v_x_5331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_boxed_5332_: u8 = 0;
    let mut v_res_5333_: *mut LeanObject = core::ptr::null_mut();
    v_enabled_boxed_5332_ = (lean_unbox(v_enabled_5329_) as u8);
    v_res_5333_ = l_Lean_Elab_InfoState_substituteLazy___lam__0(
        v_s_5327_,
        v_trees_5328_,
        v_enabled_boxed_5332_,
        v_assignment_5330_,
        v_x_5331_,
    );
    lean_dec(v_x_5331_);
    return v_res_5333_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0(
    mut v_f_5334_: *mut LeanObject,
    mut v_x1_5335_: *mut LeanObject,
    mut v_x2_5336_: *mut LeanObject,
    mut v_x3_5337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    v___x_5338_ = lean_apply_3(v_f_5334_, v_x1_5335_, v_x2_5336_, v_x3_5337_);
    return v___x_5338_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(
    mut v_f_5339_: *mut LeanObject,
    mut v_keys_5340_: *mut LeanObject,
    mut v_vals_5341_: *mut LeanObject,
    mut v_i_5342_: *mut LeanObject,
    mut v_acc_5343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: u8 = 0;
    let mut v_k_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5344_ = lean_array_get_size(v_keys_5340_);
                v___x_5345_ = lean_nat_dec_lt(v_i_5342_, v___x_5344_);
                if v___x_5345_ == 0 {
                    lean_dec(v_i_5342_);
                    lean_dec(v_f_5339_);
                    return v_acc_5343_;
                } else {
                    v_k_5346_ = lean_array_fget_borrowed(v_keys_5340_, v_i_5342_);
                    v_v_5347_ = lean_array_fget_borrowed(v_vals_5341_, v_i_5342_);
                    lean_inc(v_f_5339_);
                    lean_inc(v_v_5347_);
                    lean_inc(v_k_5346_);
                    v___x_5348_ = lean_apply_3(v_f_5339_, v_acc_5343_, v_k_5346_, v_v_5347_);
                    v___x_5349_ = lean_unsigned_to_nat(1);
                    v___x_5350_ = lean_nat_add(v_i_5342_, v___x_5349_);
                    lean_dec(v_i_5342_);
                    v_i_5342_ = v___x_5350_;
                    v_acc_5343_ = v___x_5348_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg___boxed(
    mut v_f_5352_: *mut LeanObject,
    mut v_keys_5353_: *mut LeanObject,
    mut v_vals_5354_: *mut LeanObject,
    mut v_i_5355_: *mut LeanObject,
    mut v_acc_5356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5357_: *mut LeanObject = core::ptr::null_mut();
    v_res_5357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_5352_, v_keys_5353_, v_vals_5354_, v_i_5355_, v_acc_5356_);
    lean_dec_ref(v_vals_5354_);
    lean_dec_ref(v_keys_5353_);
    return v_res_5357_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(
    mut v_f_5358_: *mut LeanObject,
    mut v_x_5359_: *mut LeanObject,
    mut v_x_5360_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5359_) == 0 {
        let mut v_es_5361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5364_: u8 = 0;
        v_es_5361_ = lean_ctor_get(v_x_5359_, 0);
        v___x_5362_ = lean_unsigned_to_nat(0);
        v___x_5363_ = lean_array_get_size(v_es_5361_);
        v___x_5364_ = lean_nat_dec_lt(v___x_5362_, v___x_5363_);
        if v___x_5364_ == 0 {
            lean_dec(v_f_5358_);
            return v_x_5360_;
        } else {
            let mut v___x_5365_: u8 = 0;
            v___x_5365_ = lean_nat_dec_le(v___x_5363_, v___x_5363_);
            if v___x_5365_ == 0 {
                if v___x_5364_ == 0 {
                    lean_dec(v_f_5358_);
                    return v_x_5360_;
                } else {
                    let mut v___x_5366_: usize = 0;
                    let mut v___x_5367_: usize = 0;
                    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5366_ = 0usize;
                    v___x_5367_ = lean_usize_of_nat(v___x_5363_);
                    v___x_5368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_5358_, v_es_5361_, v___x_5366_, v___x_5367_, v_x_5360_);
                    return v___x_5368_;
                }
            } else {
                let mut v___x_5369_: usize = 0;
                let mut v___x_5370_: usize = 0;
                let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
                v___x_5369_ = 0usize;
                v___x_5370_ = lean_usize_of_nat(v___x_5363_);
                v___x_5371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_5358_, v_es_5361_, v___x_5369_, v___x_5370_, v_x_5360_);
                return v___x_5371_;
            }
        }
    } else {
        let mut v_ks_5372_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_5373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
        v_ks_5372_ = lean_ctor_get(v_x_5359_, 0);
        v_vs_5373_ = lean_ctor_get(v_x_5359_, 1);
        v___x_5374_ = lean_unsigned_to_nat(0);
        v___x_5375_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_5358_, v_ks_5372_, v_vs_5373_, v___x_5374_, v_x_5360_);
        return v___x_5375_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(
    mut v_f_5376_: *mut LeanObject,
    mut v_as_5377_: *mut LeanObject,
    mut v_i_5378_: usize,
    mut v_stop_5379_: usize,
    mut v_b_5380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: usize = 0;
    let mut v___x_5384_: usize = 0;
    let mut v___x_5386_: u8 = 0;
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5386_ = lean_usize_dec_eq(v_i_5378_, v_stop_5379_);
                if v___x_5386_ == 0 {
                    v___x_5387_ = lean_array_uget_borrowed(v_as_5377_, v_i_5378_);
                    match lean_obj_tag(v___x_5387_) {
                        0 => {
                            v_key_5388_ = lean_ctor_get(v___x_5387_, 0);
                            v_val_5389_ = lean_ctor_get(v___x_5387_, 1);
                            lean_inc(v_f_5376_);
                            lean_inc(v_val_5389_);
                            lean_inc(v_key_5388_);
                            v___x_5390_ =
                                lean_apply_3(v_f_5376_, v_b_5380_, v_key_5388_, v_val_5389_);
                            v___y_5382_ = v___x_5390_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_5391_ = lean_ctor_get(v___x_5387_, 0);
                            lean_inc(v_f_5376_);
                            v___x_5392_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_5376_, v_node_5391_, v_b_5380_);
                            v___y_5382_ = v___x_5392_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_5382_ = v_b_5380_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_f_5376_);
                    return v_b_5380_;
                }
            }
            1 => {
                v___x_5383_ = 1usize;
                v___x_5384_ = lean_usize_add(v_i_5378_, v___x_5383_);
                v_i_5378_ = v___x_5384_;
                v_b_5380_ = v___y_5382_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg___boxed(
    mut v_f_5393_: *mut LeanObject,
    mut v_as_5394_: *mut LeanObject,
    mut v_i_5395_: *mut LeanObject,
    mut v_stop_5396_: *mut LeanObject,
    mut v_b_5397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5398_: usize = 0;
    let mut v_stop_boxed_5399_: usize = 0;
    let mut v_res_5400_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5398_ = lean_unbox_usize(v_i_5395_);
    lean_dec(v_i_5395_);
    v_stop_boxed_5399_ = lean_unbox_usize(v_stop_5396_);
    lean_dec(v_stop_5396_);
    v_res_5400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_5393_, v_as_5394_, v_i_boxed_5398_, v_stop_boxed_5399_, v_b_5397_);
    lean_dec_ref(v_as_5394_);
    return v_res_5400_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg___boxed(
    mut v_f_5401_: *mut LeanObject,
    mut v_x_5402_: *mut LeanObject,
    mut v_x_5403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5404_: *mut LeanObject = core::ptr::null_mut();
    v_res_5404_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_5401_, v_x_5402_, v_x_5403_);
    lean_dec_ref(v_x_5402_);
    return v_res_5404_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(
    mut v_map_5405_: *mut LeanObject,
    mut v_f_5406_: *mut LeanObject,
    mut v_init_5407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    v___f_5408_ = lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_5408_, 0, v_f_5406_);
    v___x_5409_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v___f_5408_, v_map_5405_, v_init_5407_);
    return v___x_5409_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg___boxed(
    mut v_map_5410_: *mut LeanObject,
    mut v_f_5411_: *mut LeanObject,
    mut v_init_5412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5413_: *mut LeanObject = core::ptr::null_mut();
    v_res_5413_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_5410_, v_f_5411_, v_init_5412_);
    lean_dec_ref(v_map_5410_);
    return v_res_5413_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___lam__0(
    mut v_ps_5414_: *mut LeanObject,
    mut v_k_5415_: *mut LeanObject,
    mut v_v_5416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    v___x_5417_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5417_, 0, v_k_5415_);
    lean_ctor_set(v___x_5417_, 1, v_v_5416_);
    v___x_5418_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5418_, 0, v___x_5417_);
    lean_ctor_set(v___x_5418_, 1, v_ps_5414_);
    return v___x_5418_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(
    mut v_m_5420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    v___f_5421_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___closed__0;
    v___x_5422_ = lean_box(0);
    v___x_5423_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_m_5420_, v___f_5421_, v___x_5422_);
    return v___x_5423_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg___boxed(
    mut v_m_5424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5425_: *mut LeanObject = core::ptr::null_mut();
    v_res_5425_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_5424_);
    lean_dec_ref(v_m_5424_);
    return v_res_5425_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(
    mut v_a_5426_: *mut LeanObject,
    mut v_a_5427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v_snd_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5426_) == 0 {
                    v___x_5428_ = l_List_reverse___redArg(v_a_5427_);
                    return v___x_5428_;
                } else {
                    v_head_5429_ = lean_ctor_get(v_a_5426_, 0);
                    v_tail_5430_ = lean_ctor_get(v_a_5426_, 1);
                    v_isSharedCheck_5439_ = (!lean_is_exclusive(v_a_5426_)) as u8;
                    if v_isSharedCheck_5439_ == 0 {
                        v___x_5432_ = v_a_5426_;
                        v_isShared_5433_ = v_isSharedCheck_5439_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5430_);
                        lean_inc(v_head_5429_);
                        lean_dec(v_a_5426_);
                        v___x_5432_ = lean_box(0);
                        v_isShared_5433_ = v_isSharedCheck_5439_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5434_ = lean_ctor_get(v_head_5429_, 1);
                lean_inc(v_snd_5434_);
                lean_dec(v_head_5429_);
                if v_isShared_5433_ == 0 {
                    lean_ctor_set(v___x_5432_, 1, v_a_5427_);
                    lean_ctor_set(v___x_5432_, 0, v_snd_5434_);
                    v___x_5436_ = v___x_5432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_snd_5434_);
                    lean_ctor_set(v_reuseFailAlloc_5438_, 1, v_a_5427_);
                    v___x_5436_ = v_reuseFailAlloc_5438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5426_ = v_tail_5430_;
                v_a_5427_ = v___x_5436_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoState_substituteLazy(
    mut v_s_5440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_5441_: u8 = 0;
    let mut v_assignment_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: u8 = 0;
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    v_enabled_5441_ = lean_ctor_get_uint8(
        v_s_5440_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_assignment_5442_ = lean_ctor_get(v_s_5440_, 0);
    lean_inc_ref(v_assignment_5442_);
    v_lazyAssignment_5443_ = lean_ctor_get(v_s_5440_, 1);
    lean_inc_ref(v_lazyAssignment_5443_);
    v_trees_5444_ = lean_ctor_get(v_s_5440_, 2);
    lean_inc_ref(v_trees_5444_);
    v___x_5445_ = lean_box((v_enabled_5441_) as usize);
    v___f_5446_ = lean_alloc_closure(
        l_Lean_Elab_InfoState_substituteLazy___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5446_, 0, v_s_5440_);
    lean_closure_set(v___f_5446_, 1, v_trees_5444_);
    lean_closure_set(v___f_5446_, 2, v___x_5445_);
    lean_closure_set(v___f_5446_, 3, v_assignment_5442_);
    v___x_5447_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_lazyAssignment_5443_);
    lean_dec_ref(v_lazyAssignment_5443_);
    v___x_5448_ = lean_box(0);
    v___x_5449_ = l_List_mapTR_loop___at___00Lean_Elab_InfoState_substituteLazy_spec__3(
        v___x_5447_,
        v___x_5448_,
    );
    v___x_5450_ = lean_unsigned_to_nat(0);
    v___x_5451_ = 0;
    v___x_5452_ = l_Task_mapList___redArg(v___f_5446_, v___x_5449_, v___x_5450_, v___x_5451_);
    return v___x_5452_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0(
    mut v_00_u03b2_5453_: *mut LeanObject,
    mut v_00_u03c3_5454_: *mut LeanObject,
    mut v_pm_5455_: *mut LeanObject,
    mut v_f_5456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    v___x_5457_ =
        l_Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0___redArg(
            v_pm_5455_, v_f_5456_,
        );
    return v___x_5457_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(
    mut v_00_u03b2_5458_: *mut LeanObject,
    mut v_m_5459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    v___x_5460_ = l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___redArg(v_m_5459_);
    return v___x_5460_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2___boxed(
    mut v_00_u03b2_5461_: *mut LeanObject,
    mut v_m_5462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5463_: *mut LeanObject = core::ptr::null_mut();
    v_res_5463_ =
        l_Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2(
            v_00_u03b2_5461_,
            v_m_5462_,
        );
    lean_dec_ref(v_m_5462_);
    return v_res_5463_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0___redArg(
    mut v_pm_5464_: *mut LeanObject,
    mut v_f_5465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    v___x_5466_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_5465_, v_pm_5464_);
    return v___x_5466_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0(
    mut v_00_u03b2_5467_: *mut LeanObject,
    mut v_00_u03c3_5468_: *mut LeanObject,
    mut v_pm_5469_: *mut LeanObject,
    mut v_f_5470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    v___x_5471_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_5470_, v_pm_5469_);
    return v___x_5471_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(
    mut v_00_u03c3_5472_: *mut LeanObject,
    mut v_00_u03b2_5473_: *mut LeanObject,
    mut v_map_5474_: *mut LeanObject,
    mut v_f_5475_: *mut LeanObject,
    mut v_init_5476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    v___x_5477_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___redArg(v_map_5474_, v_f_5475_, v_init_5476_);
    return v___x_5477_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5___boxed(
    mut v_00_u03c3_5478_: *mut LeanObject,
    mut v_00_u03b2_5479_: *mut LeanObject,
    mut v_map_5480_: *mut LeanObject,
    mut v_f_5481_: *mut LeanObject,
    mut v_init_5482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5483_: *mut LeanObject = core::ptr::null_mut();
    v_res_5483_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5(v_00_u03c3_5478_, v_00_u03b2_5479_, v_map_5480_, v_f_5481_, v_init_5482_);
    lean_dec_ref(v_map_5480_);
    return v_res_5483_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5484_: *mut LeanObject,
    mut v_00_u03b2_5485_: *mut LeanObject,
    mut v_00_u03c3_5486_: *mut LeanObject,
    mut v_f_5487_: *mut LeanObject,
    mut v_n_5488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    v___x_5489_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1___redArg(v_f_5487_, v_n_5488_);
    return v___x_5489_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(
    mut v_map_5490_: *mut LeanObject,
    mut v_f_5491_: *mut LeanObject,
    mut v_init_5492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    v___x_5493_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_5491_, v_map_5490_, v_init_5492_);
    return v___x_5493_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_map_5494_: *mut LeanObject,
    mut v_f_5495_: *mut LeanObject,
    mut v_init_5496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5497_: *mut LeanObject = core::ptr::null_mut();
    v_res_5497_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___redArg(v_map_5494_, v_f_5495_, v_init_5496_);
    lean_dec_ref(v_map_5494_);
    return v_res_5497_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(
    mut v_00_u03c3_5498_: *mut LeanObject,
    mut v_00_u03b2_5499_: *mut LeanObject,
    mut v_map_5500_: *mut LeanObject,
    mut v_f_5501_: *mut LeanObject,
    mut v_init_5502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    v___x_5503_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_5501_, v_map_5500_, v_init_5502_);
    return v___x_5503_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03c3_5504_: *mut LeanObject,
    mut v_00_u03b2_5505_: *mut LeanObject,
    mut v_map_5506_: *mut LeanObject,
    mut v_f_5507_: *mut LeanObject,
    mut v_init_5508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5509_: *mut LeanObject = core::ptr::null_mut();
    v_res_5509_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8(v_00_u03c3_5504_, v_00_u03b2_5505_, v_map_5506_, v_f_5507_, v_init_5508_);
    lean_dec_ref(v_map_5506_);
    return v_res_5509_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b1_5510_: *mut LeanObject,
    mut v_00_u03b2_5511_: *mut LeanObject,
    mut v_00_u03c3_5512_: *mut LeanObject,
    mut v_f_5513_: *mut LeanObject,
    mut v_sz_5514_: usize,
    mut v_i_5515_: usize,
    mut v_bs_5516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    v___x_5517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___redArg(v_f_5513_, v_sz_5514_, v_i_5515_, v_bs_5516_);
    return v___x_5517_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b1_5518_: *mut LeanObject,
    mut v_00_u03b2_5519_: *mut LeanObject,
    mut v_00_u03c3_5520_: *mut LeanObject,
    mut v_f_5521_: *mut LeanObject,
    mut v_sz_5522_: *mut LeanObject,
    mut v_i_5523_: *mut LeanObject,
    mut v_bs_5524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5525_: usize = 0;
    let mut v_i_boxed_5526_: usize = 0;
    let mut v_res_5527_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5525_ = lean_unbox_usize(v_sz_5522_);
    lean_dec(v_sz_5522_);
    v_i_boxed_5526_ = lean_unbox_usize(v_i_5523_);
    lean_dec(v_i_5523_);
    v_res_5527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_5518_, v_00_u03b2_5519_, v_00_u03c3_5520_, v_f_5521_, v_sz_boxed_5525_, v_i_boxed_5526_, v_bs_5524_);
    return v_res_5527_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03b1_5528_: *mut LeanObject,
    mut v_00_u03b2_5529_: *mut LeanObject,
    mut v_f_5530_: *mut LeanObject,
    mut v_as_5531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    v___x_5532_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___redArg(v_f_5530_, v_as_5531_);
    return v___x_5532_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03b1_5533_: *mut LeanObject,
    mut v_00_u03b2_5534_: *mut LeanObject,
    mut v_f_5535_: *mut LeanObject,
    mut v_as_5536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5537_: *mut LeanObject = core::ptr::null_mut();
    v_res_5537_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_5533_, v_00_u03b2_5534_, v_f_5535_, v_as_5536_);
    lean_dec_ref(v_as_5536_);
    return v_res_5537_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(
    mut v_00_u03c3_5538_: *mut LeanObject,
    mut v_00_u03b1_5539_: *mut LeanObject,
    mut v_00_u03b2_5540_: *mut LeanObject,
    mut v_f_5541_: *mut LeanObject,
    mut v_x_5542_: *mut LeanObject,
    mut v_x_5543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    v___x_5544_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___redArg(v_f_5541_, v_x_5542_, v_x_5543_);
    return v___x_5544_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12___boxed(
    mut v_00_u03c3_5545_: *mut LeanObject,
    mut v_00_u03b1_5546_: *mut LeanObject,
    mut v_00_u03b2_5547_: *mut LeanObject,
    mut v_f_5548_: *mut LeanObject,
    mut v_x_5549_: *mut LeanObject,
    mut v_x_5550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5551_: *mut LeanObject = core::ptr::null_mut();
    v_res_5551_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12(v_00_u03c3_5545_, v_00_u03b1_5546_, v_00_u03b2_5547_, v_f_5548_, v_x_5549_, v_x_5550_);
    lean_dec_ref(v_x_5549_);
    return v_res_5551_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(
    mut v_00_u03b1_5552_: *mut LeanObject,
    mut v_00_u03b2_5553_: *mut LeanObject,
    mut v_f_5554_: *mut LeanObject,
    mut v_as_5555_: *mut LeanObject,
    mut v_i_5556_: *mut LeanObject,
    mut v_acc_5557_: *mut LeanObject,
    mut v_hle_5558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    v___x_5559_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_f_5554_, v_as_5555_, v_i_5556_, v_acc_5557_);
    return v___x_5559_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10___boxed(
    mut v_00_u03b1_5560_: *mut LeanObject,
    mut v_00_u03b2_5561_: *mut LeanObject,
    mut v_f_5562_: *mut LeanObject,
    mut v_as_5563_: *mut LeanObject,
    mut v_i_5564_: *mut LeanObject,
    mut v_acc_5565_: *mut LeanObject,
    mut v_hle_5566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5567_: *mut LeanObject = core::ptr::null_mut();
    v_res_5567_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Elab_InfoState_substituteLazy_spec__0_spec__0_spec__1_spec__6_spec__10(v_00_u03b1_5560_, v_00_u03b2_5561_, v_f_5562_, v_as_5563_, v_i_5564_, v_acc_5565_, v_hle_5566_);
    lean_dec_ref(v_as_5563_);
    return v_res_5567_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(
    mut v_00_u03b1_5568_: *mut LeanObject,
    mut v_00_u03b2_5569_: *mut LeanObject,
    mut v_00_u03c3_5570_: *mut LeanObject,
    mut v_f_5571_: *mut LeanObject,
    mut v_as_5572_: *mut LeanObject,
    mut v_i_5573_: usize,
    mut v_stop_5574_: usize,
    mut v_b_5575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    v___x_5576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___redArg(v_f_5571_, v_as_5572_, v_i_5573_, v_stop_5574_, v_b_5575_);
    return v___x_5576_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14___boxed(
    mut v_00_u03b1_5577_: *mut LeanObject,
    mut v_00_u03b2_5578_: *mut LeanObject,
    mut v_00_u03c3_5579_: *mut LeanObject,
    mut v_f_5580_: *mut LeanObject,
    mut v_as_5581_: *mut LeanObject,
    mut v_i_5582_: *mut LeanObject,
    mut v_stop_5583_: *mut LeanObject,
    mut v_b_5584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5585_: usize = 0;
    let mut v_stop_boxed_5586_: usize = 0;
    let mut v_res_5587_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5585_ = lean_unbox_usize(v_i_5582_);
    lean_dec(v_i_5582_);
    v_stop_boxed_5586_ = lean_unbox_usize(v_stop_5583_);
    lean_dec(v_stop_5583_);
    v_res_5587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__14(v_00_u03b1_5577_, v_00_u03b2_5578_, v_00_u03c3_5579_, v_f_5580_, v_as_5581_, v_i_boxed_5585_, v_stop_boxed_5586_, v_b_5584_);
    lean_dec_ref(v_as_5581_);
    return v_res_5587_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(
    mut v_00_u03c3_5588_: *mut LeanObject,
    mut v_00_u03b1_5589_: *mut LeanObject,
    mut v_00_u03b2_5590_: *mut LeanObject,
    mut v_f_5591_: *mut LeanObject,
    mut v_keys_5592_: *mut LeanObject,
    mut v_vals_5593_: *mut LeanObject,
    mut v_heq_5594_: *mut LeanObject,
    mut v_i_5595_: *mut LeanObject,
    mut v_acc_5596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    v___x_5597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___redArg(v_f_5591_, v_keys_5592_, v_vals_5593_, v_i_5595_, v_acc_5596_);
    return v___x_5597_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15___boxed(
    mut v_00_u03c3_5598_: *mut LeanObject,
    mut v_00_u03b1_5599_: *mut LeanObject,
    mut v_00_u03b2_5600_: *mut LeanObject,
    mut v_f_5601_: *mut LeanObject,
    mut v_keys_5602_: *mut LeanObject,
    mut v_vals_5603_: *mut LeanObject,
    mut v_heq_5604_: *mut LeanObject,
    mut v_i_5605_: *mut LeanObject,
    mut v_acc_5606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5607_: *mut LeanObject = core::ptr::null_mut();
    v_res_5607_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_Elab_InfoState_substituteLazy_spec__2_spec__5_spec__8_spec__12_spec__15(v_00_u03c3_5598_, v_00_u03b1_5599_, v_00_u03b2_5600_, v_f_5601_, v_keys_5602_, v_vals_5603_, v_heq_5604_, v_i_5605_, v_acc_5606_);
    lean_dec_ref(v_vals_5603_);
    lean_dec_ref(v_keys_5602_);
    return v_res_5607_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(
    mut v_opts_5608_: *mut LeanObject,
    mut v_opt_5609_: *mut LeanObject,
) -> u8 {
    let mut v_name_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    v_name_5610_ = lean_ctor_get(v_opt_5609_, 0);
    v_defValue_5611_ = lean_ctor_get(v_opt_5609_, 1);
    v_map_5612_ = lean_ctor_get(v_opts_5608_, 0);
    v___x_5613_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5612_,
            v_name_5610_,
        );
    if lean_obj_tag(v___x_5613_) == 0 {
        let mut v___x_5614_: u8 = 0;
        v___x_5614_ = (lean_unbox(v_defValue_5611_) as u8);
        return v___x_5614_;
    } else {
        let mut v_val_5615_: *mut LeanObject = core::ptr::null_mut();
        v_val_5615_ = lean_ctor_get(v___x_5613_, 0);
        lean_inc(v_val_5615_);
        lean_dec_ref_known(v___x_5613_, 1);
        if lean_obj_tag(v_val_5615_) == 1 {
            let mut v_v_5616_: u8 = 0;
            v_v_5616_ = lean_ctor_get_uint8(v_val_5615_, 0 as u32);
            lean_dec_ref_known(v_val_5615_, 0);
            return v_v_5616_;
        } else {
            let mut v___x_5617_: u8 = 0;
            lean_dec(v_val_5615_);
            v___x_5617_ = (lean_unbox(v_defValue_5611_) as u8);
            return v___x_5617_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(
    mut v_opts_5618_: *mut LeanObject,
    mut v_opt_5619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5620_: u8 = 0;
    let mut v_r_5621_: *mut LeanObject = core::ptr::null_mut();
    v_res_5620_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(
        v_opts_5618_,
        v_opt_5619_,
    );
    lean_dec_ref(v_opt_5619_);
    lean_dec_ref(v_opts_5618_);
    v_r_5621_ = lean_box((v_res_5620_) as usize);
    return v_r_5621_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(
    mut v_opts_5622_: *mut LeanObject,
    mut v_opt_5623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    v_name_5624_ = lean_ctor_get(v_opt_5623_, 0);
    v_defValue_5625_ = lean_ctor_get(v_opt_5623_, 1);
    v_map_5626_ = lean_ctor_get(v_opts_5622_, 0);
    v___x_5627_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5626_,
            v_name_5624_,
        );
    if lean_obj_tag(v___x_5627_) == 0 {
        lean_inc(v_defValue_5625_);
        return v_defValue_5625_;
    } else {
        let mut v_val_5628_: *mut LeanObject = core::ptr::null_mut();
        v_val_5628_ = lean_ctor_get(v___x_5627_, 0);
        lean_inc(v_val_5628_);
        lean_dec_ref_known(v___x_5627_, 1);
        if lean_obj_tag(v_val_5628_) == 3 {
            let mut v_v_5629_: *mut LeanObject = core::ptr::null_mut();
            v_v_5629_ = lean_ctor_get(v_val_5628_, 0);
            lean_inc(v_v_5629_);
            lean_dec_ref_known(v_val_5628_, 1);
            return v_v_5629_;
        } else {
            lean_dec(v_val_5628_);
            lean_inc(v_defValue_5625_);
            return v_defValue_5625_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(
    mut v_opts_5630_: *mut LeanObject,
    mut v_opt_5631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5632_: *mut LeanObject = core::ptr::null_mut();
    v_res_5632_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(
        v_opts_5630_,
        v_opt_5631_,
    );
    lean_dec_ref(v_opt_5631_);
    lean_dec_ref(v_opts_5630_);
    return v_res_5632_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    v___x_5633_ = lean_unsigned_to_nat(32);
    v___x_5634_ = lean_mk_empty_array_with_capacity(v___x_5633_);
    v___x_5635_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5635_, 0, v___x_5634_);
    return v___x_5635_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_5636_: usize = 0;
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    v___x_5636_ = 5usize;
    v___x_5637_ = lean_unsigned_to_nat(0);
    v___x_5638_ = lean_unsigned_to_nat(32);
    v___x_5639_ = lean_mk_empty_array_with_capacity(v___x_5638_);
    v___x_5640_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once),
        _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0,
    );
    v___x_5641_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5641_, 0, v___x_5640_);
    lean_ctor_set(v___x_5641_, 1, v___x_5639_);
    lean_ctor_set(v___x_5641_, 2, v___x_5637_);
    lean_ctor_set(v___x_5641_, 3, v___x_5637_);
    lean_ctor_set_usize(v___x_5641_, 4, v___x_5636_);
    return v___x_5641_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    v___x_5642_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5642_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    v___x_5643_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once),
        _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2,
    );
    v___x_5644_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5644_, 0, v___x_5643_);
    return v___x_5644_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    v___x_5645_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once),
        _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3,
    );
    v___x_5646_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5646_, 0, v___x_5645_);
    lean_ctor_set(v___x_5646_, 1, v___x_5645_);
    return v___x_5646_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    v___x_5647_ = l_Lean_NameSet_empty;
    v___x_5648_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once),
        _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1,
    );
    v___x_5649_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5649_, 0, v___x_5648_);
    lean_ctor_set(v___x_5649_, 1, v___x_5648_);
    lean_ctor_set(v___x_5649_, 2, v___x_5647_);
    return v___x_5649_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    v___x_5650_ = lean_unsigned_to_nat(1);
    v___x_5651_ = l_Lean_firstFrontendMacroScope;
    v___x_5652_ = lean_nat_add(v___x_5651_, v___x_5650_);
    return v___x_5652_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: u64 = 0;
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    v___x_5657_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once),
        _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1,
    );
    v___x_5658_ = 0u64;
    v___x_5659_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_5659_, 0, v___x_5657_);
    lean_ctor_set_uint64(
        v___x_5659_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5658_,
    );
    return v___x_5659_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: u8 = 0;
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    v___x_5660_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once),
        _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1,
    );
    v___x_5661_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once),
        _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3,
    );
    v___x_5662_ = 1;
    v___x_5663_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_5663_, 0, v___x_5661_);
    lean_ctor_set(v___x_5663_, 1, v___x_5661_);
    lean_ctor_set(v___x_5663_, 2, v___x_5660_);
    lean_ctor_set_uint8(
        v___x_5663_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_5662_,
    );
    return v___x_5663_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13() -> *mut LeanObject {
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    v___x_5668_ = l_Lean_Options_empty;
    v___x_5669_ = l_Lean_Core_getMaxHeartbeats(v___x_5668_);
    return v___x_5669_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14() -> u8 {
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: u8 = 0;
    v___x_5670_ = l_Lean_diagnostics;
    v___x_5671_ = l_Lean_Options_empty;
    v___x_5672_ =
        l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_5671_, v___x_5670_);
    return v___x_5672_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15() -> *mut LeanObject {
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    v___x_5673_ = l_Lean_maxRecDepth;
    v___x_5674_ = l_Lean_Options_empty;
    v___x_5675_ =
        l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v___x_5674_, v___x_5673_);
    return v___x_5675_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_runCoreM___redArg(
    mut v_info_5676_: *mut LeanObject,
    mut v_x_5677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: u8 = 0;
    let mut v_env_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5701_: u8 = 0;
    let mut v___y_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5714_: u8 = 0;
    let mut v_inheritedTraceOptions_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5723_: u8 = 0;
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5728_: u8 = 0;
    let mut v_a_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v_msg_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5747_: u8 = 0;
    let mut v___y_5749_: u8 = 0;
    let mut v___y_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5764_: u8 = 0;
    let mut v_inheritedTraceOptions_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5767_: u8 = 0;
    let mut v___y_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5771_: u8 = 0;
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5789_: u8 = 0;
    let mut v_unused_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: u8 = 0;
    let mut v___y_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5820_: u8 = 0;
    let mut v_inheritedTraceOptions_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5824_: u8 = 0;
    let mut v_env_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: u8 = 0;
    let mut v___x_5831_: u8 = 0;
    let mut v_reuseFailAlloc_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut v_unused_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5837_: u8 = 0;
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5849_: u8 = 0;
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_unused_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5679_ = lean_unsigned_to_nat(0);
                v___x_5680_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4,
                );
                v___x_5681_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5,
                );
                v___x_5682_ = lean_io_get_num_heartbeats();
                v_toCommandContextInfo_5683_ = lean_ctor_get(v_info_5676_, 0);
                lean_inc_ref(v_toCommandContextInfo_5683_);
                lean_dec_ref(v_info_5676_);
                v_env_5684_ = lean_ctor_get(v_toCommandContextInfo_5683_, 0);
                lean_inc_ref(v_env_5684_);
                v_options_5685_ = lean_ctor_get(v_toCommandContextInfo_5683_, 4);
                lean_inc_ref(v_options_5685_);
                v_currNamespace_5686_ = lean_ctor_get(v_toCommandContextInfo_5683_, 5);
                lean_inc(v_currNamespace_5686_);
                v_openDecls_5687_ = lean_ctor_get(v_toCommandContextInfo_5683_, 6);
                lean_inc(v_openDecls_5687_);
                v_ngen_5688_ = lean_ctor_get(v_toCommandContextInfo_5683_, 7);
                lean_inc_ref(v_ngen_5688_);
                lean_dec_ref(v_toCommandContextInfo_5683_);
                v___x_5689_ = l_Lean_firstFrontendMacroScope;
                v___x_5690_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6,
                );
                v___x_5691_ = 0;
                v_env_5692_ = l_Lean_Environment_setExporting(v_env_5684_, v___x_5691_);
                v___x_5693_ = lean_box(0);
                v___x_5694_ = l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7;
                v___x_5695_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8,
                );
                v___x_5696_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9,
                );
                v___x_5697_ = l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10;
                v___x_5698_ = lean_alloc_ctor(0, 9, (0) as u32);
                lean_ctor_set(v___x_5698_, 0, v_env_5692_);
                lean_ctor_set(v___x_5698_, 1, v___x_5690_);
                lean_ctor_set(v___x_5698_, 2, v_ngen_5688_);
                lean_ctor_set(v___x_5698_, 3, v___x_5694_);
                lean_ctor_set(v___x_5698_, 4, v___x_5695_);
                lean_ctor_set(v___x_5698_, 5, v___x_5680_);
                lean_ctor_set(v___x_5698_, 6, v___x_5681_);
                lean_ctor_set(v___x_5698_, 7, v___x_5696_);
                lean_ctor_set(v___x_5698_, 8, v___x_5697_);
                v___x_5699_ = lean_st_mk_ref(v___x_5698_);
                v___x_5791_ = l_Lean_inheritedTraceOptions;
                v___x_5792_ = lean_st_ref_get(v___x_5791_);
                v___x_5793_ = lean_st_ref_get(v___x_5699_);
                v___x_5794_ = l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12;
                v___x_5795_ = l_Lean_instInhabitedFileMap_default;
                v___x_5796_ = l_Lean_Options_empty;
                v___x_5797_ = lean_unsigned_to_nat(1000);
                v___x_5798_ = lean_box(0);
                v___x_5799_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13,
                );
                v___x_5800_ = lean_box(0);
                v___x_5801_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5801_, 0, v___x_5794_);
                lean_ctor_set(v___x_5801_, 1, v___x_5795_);
                lean_ctor_set(v___x_5801_, 2, v___x_5796_);
                lean_ctor_set(v___x_5801_, 3, v___x_5679_);
                lean_ctor_set(v___x_5801_, 4, v___x_5797_);
                lean_ctor_set(v___x_5801_, 5, v___x_5798_);
                lean_ctor_set(v___x_5801_, 6, v_currNamespace_5686_);
                lean_ctor_set(v___x_5801_, 7, v_openDecls_5687_);
                lean_ctor_set(v___x_5801_, 8, v___x_5682_);
                lean_ctor_set(v___x_5801_, 9, v___x_5799_);
                lean_ctor_set(v___x_5801_, 10, v___x_5693_);
                lean_ctor_set(v___x_5801_, 11, v___x_5689_);
                lean_ctor_set(v___x_5801_, 12, v___x_5800_);
                lean_ctor_set(v___x_5801_, 13, v___x_5792_);
                lean_ctor_set_uint8(
                    v___x_5801_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_5691_,
                );
                lean_ctor_set_uint8(
                    v___x_5801_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v___x_5691_,
                );
                v_env_5802_ = lean_ctor_get(v___x_5793_, 0);
                lean_inc_ref(v_env_5802_);
                lean_dec(v___x_5793_);
                v___x_5803_ = l_Lean_diagnostics;
                v___x_5804_ = lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14,
                );
                v___x_5857_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5802_);
                lean_dec_ref(v_env_5802_);
                if v___x_5857_ == 0 {
                    if v___x_5804_ == 0 {
                        lean_inc(v___x_5699_);
                        v___y_5806_ = v___x_5801_;
                        v___y_5807_ = v___x_5699_;
                        state = 11;
                        continue;
                    } else {
                        v___y_5837_ = v___x_5857_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___y_5837_ = v___x_5804_;
                    state = 14;
                    continue;
                }
            }
            1 => {
                v___x_5717_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(
                    v_options_5685_,
                    v___y_5702_,
                );
                v___x_5718_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5718_, 0, v_fileName_5703_);
                lean_ctor_set(v___x_5718_, 1, v_fileMap_5704_);
                lean_ctor_set(v___x_5718_, 2, v_options_5685_);
                lean_ctor_set(v___x_5718_, 3, v_currRecDepth_5705_);
                lean_ctor_set(v___x_5718_, 4, v___x_5717_);
                lean_ctor_set(v___x_5718_, 5, v_ref_5706_);
                lean_ctor_set(v___x_5718_, 6, v_currNamespace_5707_);
                lean_ctor_set(v___x_5718_, 7, v_openDecls_5708_);
                lean_ctor_set(v___x_5718_, 8, v_initHeartbeats_5709_);
                lean_ctor_set(v___x_5718_, 9, v_maxHeartbeats_5710_);
                lean_ctor_set(v___x_5718_, 10, v_quotContext_5711_);
                lean_ctor_set(v___x_5718_, 11, v_currMacroScope_5712_);
                lean_ctor_set(v___x_5718_, 12, v_cancelTk_x3f_5713_);
                lean_ctor_set(v___x_5718_, 13, v_inheritedTraceOptions_5715_);
                lean_ctor_set_uint8(
                    v___x_5718_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_5701_,
                );
                lean_ctor_set_uint8(
                    v___x_5718_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5714_,
                );
                v___x_5719_ = lean_apply_3(v_x_5677_, v___x_5718_, v___y_5716_, lean_box(0));
                if lean_obj_tag(v___x_5719_) == 0 {
                    v_a_5720_ = lean_ctor_get(v___x_5719_, 0);
                    v_isSharedCheck_5728_ = (!lean_is_exclusive(v___x_5719_)) as u8;
                    if v_isSharedCheck_5728_ == 0 {
                        v___x_5722_ = v___x_5719_;
                        v_isShared_5723_ = v_isSharedCheck_5728_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5720_);
                        lean_dec(v___x_5719_);
                        v___x_5722_ = lean_box(0);
                        v_isShared_5723_ = v_isSharedCheck_5728_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5699_);
                    v_a_5729_ = lean_ctor_get(v___x_5719_, 0);
                    v_isSharedCheck_5747_ = (!lean_is_exclusive(v___x_5719_)) as u8;
                    if v_isSharedCheck_5747_ == 0 {
                        v___x_5731_ = v___x_5719_;
                        v_isShared_5732_ = v_isSharedCheck_5747_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5729_);
                        lean_dec(v___x_5719_);
                        v___x_5731_ = lean_box(0);
                        v_isShared_5732_ = v_isSharedCheck_5747_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5724_ = lean_st_ref_get(v___x_5699_);
                lean_dec(v___x_5699_);
                lean_dec(v___x_5724_);
                if v_isShared_5723_ == 0 {
                    v___x_5726_ = v___x_5722_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_a_5720_);
                    v___x_5726_ = v_reuseFailAlloc_5727_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5726_;
            }
            4 => {
                if lean_obj_tag(v_a_5729_) == 0 {
                    v_msg_5733_ = lean_ctor_get(v_a_5729_, 1);
                    lean_inc_ref(v_msg_5733_);
                    lean_dec_ref_known(v_a_5729_, 2);
                    v___x_5734_ = l_Lean_MessageData_toString(v_msg_5733_);
                    v___x_5735_ = lean_mk_io_user_error(v___x_5734_);
                    if v_isShared_5732_ == 0 {
                        lean_ctor_set(v___x_5731_, 0, v___x_5735_);
                        v___x_5737_ = v___x_5731_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5738_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5738_, 0, v___x_5735_);
                        v___x_5737_ = v_reuseFailAlloc_5738_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_id_5739_ = lean_ctor_get(v_a_5729_, 0);
                    lean_inc(v_id_5739_);
                    lean_dec_ref_known(v_a_5729_, 2);
                    v___x_5740_ = l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11;
                    v___x_5741_ = l_Nat_reprFast(v_id_5739_);
                    v___x_5742_ = lean_string_append(v___x_5740_, v___x_5741_);
                    lean_dec_ref(v___x_5741_);
                    v___x_5743_ = lean_mk_io_user_error(v___x_5742_);
                    if v_isShared_5732_ == 0 {
                        lean_ctor_set(v___x_5731_, 0, v___x_5743_);
                        v___x_5745_ = v___x_5731_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5746_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5746_, 0, v___x_5743_);
                        v___x_5745_ = v_reuseFailAlloc_5746_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5737_;
            }
            6 => {
                return v___x_5745_;
            }
            7 => {
                v_fileName_5753_ = lean_ctor_get(v___y_5751_, 0);
                lean_inc_ref(v_fileName_5753_);
                v_fileMap_5754_ = lean_ctor_get(v___y_5751_, 1);
                lean_inc_ref(v_fileMap_5754_);
                v_currRecDepth_5755_ = lean_ctor_get(v___y_5751_, 3);
                lean_inc(v_currRecDepth_5755_);
                v_ref_5756_ = lean_ctor_get(v___y_5751_, 5);
                lean_inc(v_ref_5756_);
                v_currNamespace_5757_ = lean_ctor_get(v___y_5751_, 6);
                lean_inc(v_currNamespace_5757_);
                v_openDecls_5758_ = lean_ctor_get(v___y_5751_, 7);
                lean_inc(v_openDecls_5758_);
                v_initHeartbeats_5759_ = lean_ctor_get(v___y_5751_, 8);
                lean_inc(v_initHeartbeats_5759_);
                v_maxHeartbeats_5760_ = lean_ctor_get(v___y_5751_, 9);
                lean_inc(v_maxHeartbeats_5760_);
                v_quotContext_5761_ = lean_ctor_get(v___y_5751_, 10);
                lean_inc(v_quotContext_5761_);
                v_currMacroScope_5762_ = lean_ctor_get(v___y_5751_, 11);
                lean_inc(v_currMacroScope_5762_);
                v_cancelTk_x3f_5763_ = lean_ctor_get(v___y_5751_, 12);
                lean_inc(v_cancelTk_x3f_5763_);
                v_suppressElabErrors_5764_ = lean_ctor_get_uint8(
                    v___y_5751_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5765_ = lean_ctor_get(v___y_5751_, 13);
                lean_inc_ref(v_inheritedTraceOptions_5765_);
                lean_dec_ref(v___y_5751_);
                v___y_5701_ = v___y_5749_;
                v___y_5702_ = v___y_5750_;
                v_fileName_5703_ = v_fileName_5753_;
                v_fileMap_5704_ = v_fileMap_5754_;
                v_currRecDepth_5705_ = v_currRecDepth_5755_;
                v_ref_5706_ = v_ref_5756_;
                v_currNamespace_5707_ = v_currNamespace_5757_;
                v_openDecls_5708_ = v_openDecls_5758_;
                v_initHeartbeats_5709_ = v_initHeartbeats_5759_;
                v_maxHeartbeats_5710_ = v_maxHeartbeats_5760_;
                v_quotContext_5711_ = v_quotContext_5761_;
                v_currMacroScope_5712_ = v_currMacroScope_5762_;
                v_cancelTk_x3f_5713_ = v_cancelTk_x3f_5763_;
                v_suppressElabErrors_5714_ = v_suppressElabErrors_5764_;
                v_inheritedTraceOptions_5715_ = v_inheritedTraceOptions_5765_;
                v___y_5716_ = v___y_5752_;
                state = 1;
                continue;
            }
            8 => {
                if v___y_5771_ == 0 {
                    v___x_5772_ = lean_st_ref_take(v___y_5769_);
                    v_env_5773_ = lean_ctor_get(v___x_5772_, 0);
                    v_nextMacroScope_5774_ = lean_ctor_get(v___x_5772_, 1);
                    v_ngen_5775_ = lean_ctor_get(v___x_5772_, 2);
                    v_auxDeclNGen_5776_ = lean_ctor_get(v___x_5772_, 3);
                    v_traceState_5777_ = lean_ctor_get(v___x_5772_, 4);
                    v_messages_5778_ = lean_ctor_get(v___x_5772_, 6);
                    v_infoState_5779_ = lean_ctor_get(v___x_5772_, 7);
                    v_snapshotTasks_5780_ = lean_ctor_get(v___x_5772_, 8);
                    v_isSharedCheck_5789_ = (!lean_is_exclusive(v___x_5772_)) as u8;
                    if v_isSharedCheck_5789_ == 0 {
                        v_unused_5790_ = lean_ctor_get(v___x_5772_, 5);
                        lean_dec(v_unused_5790_);
                        v___x_5782_ = v___x_5772_;
                        v_isShared_5783_ = v_isSharedCheck_5789_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_5780_);
                        lean_inc(v_infoState_5779_);
                        lean_inc(v_messages_5778_);
                        lean_inc(v_traceState_5777_);
                        lean_inc(v_auxDeclNGen_5776_);
                        lean_inc(v_ngen_5775_);
                        lean_inc(v_nextMacroScope_5774_);
                        lean_inc(v_env_5773_);
                        lean_dec(v___x_5772_);
                        v___x_5782_ = lean_box(0);
                        v_isShared_5783_ = v_isSharedCheck_5789_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___y_5749_ = v___y_5767_;
                    v___y_5750_ = v___y_5768_;
                    v___y_5751_ = v___y_5770_;
                    v___y_5752_ = v___y_5769_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_5784_ = l_Lean_Kernel_enableDiag(v_env_5773_, v___y_5767_);
                if v_isShared_5783_ == 0 {
                    lean_ctor_set(v___x_5782_, 5, v___x_5680_);
                    lean_ctor_set(v___x_5782_, 0, v___x_5784_);
                    v___x_5786_ = v___x_5782_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5788_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 0, v___x_5784_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 1, v_nextMacroScope_5774_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 2, v_ngen_5775_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 3, v_auxDeclNGen_5776_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 4, v_traceState_5777_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 5, v___x_5680_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 6, v_messages_5778_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 7, v_infoState_5779_);
                    lean_ctor_set(v_reuseFailAlloc_5788_, 8, v_snapshotTasks_5780_);
                    v___x_5786_ = v_reuseFailAlloc_5788_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5787_ = lean_st_ref_set(v___y_5769_, v___x_5786_);
                v___y_5749_ = v___y_5767_;
                v___y_5750_ = v___y_5768_;
                v___y_5751_ = v___y_5770_;
                v___y_5752_ = v___y_5769_;
                state = 7;
                continue;
            }
            11 => {
                v___x_5808_ = lean_st_ref_get(v___y_5807_);
                v_fileName_5809_ = lean_ctor_get(v___y_5806_, 0);
                v_fileMap_5810_ = lean_ctor_get(v___y_5806_, 1);
                v_currRecDepth_5811_ = lean_ctor_get(v___y_5806_, 3);
                v_ref_5812_ = lean_ctor_get(v___y_5806_, 5);
                v_currNamespace_5813_ = lean_ctor_get(v___y_5806_, 6);
                v_openDecls_5814_ = lean_ctor_get(v___y_5806_, 7);
                v_initHeartbeats_5815_ = lean_ctor_get(v___y_5806_, 8);
                v_maxHeartbeats_5816_ = lean_ctor_get(v___y_5806_, 9);
                v_quotContext_5817_ = lean_ctor_get(v___y_5806_, 10);
                v_currMacroScope_5818_ = lean_ctor_get(v___y_5806_, 11);
                v_cancelTk_x3f_5819_ = lean_ctor_get(v___y_5806_, 12);
                v_suppressElabErrors_5820_ = lean_ctor_get_uint8(
                    v___y_5806_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5821_ = lean_ctor_get(v___y_5806_, 13);
                v_isSharedCheck_5833_ = (!lean_is_exclusive(v___y_5806_)) as u8;
                if v_isSharedCheck_5833_ == 0 {
                    v_unused_5834_ = lean_ctor_get(v___y_5806_, 4);
                    lean_dec(v_unused_5834_);
                    v_unused_5835_ = lean_ctor_get(v___y_5806_, 2);
                    lean_dec(v_unused_5835_);
                    v___x_5823_ = v___y_5806_;
                    v_isShared_5824_ = v_isSharedCheck_5833_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_5821_);
                    lean_inc(v_cancelTk_x3f_5819_);
                    lean_inc(v_currMacroScope_5818_);
                    lean_inc(v_quotContext_5817_);
                    lean_inc(v_maxHeartbeats_5816_);
                    lean_inc(v_initHeartbeats_5815_);
                    lean_inc(v_openDecls_5814_);
                    lean_inc(v_currNamespace_5813_);
                    lean_inc(v_ref_5812_);
                    lean_inc(v_currRecDepth_5811_);
                    lean_inc(v_fileMap_5810_);
                    lean_inc(v_fileName_5809_);
                    lean_dec(v___y_5806_);
                    v___x_5823_ = lean_box(0);
                    v_isShared_5824_ = v_isSharedCheck_5833_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_env_5825_ = lean_ctor_get(v___x_5808_, 0);
                lean_inc_ref(v_env_5825_);
                lean_dec(v___x_5808_);
                v___x_5826_ = l_Lean_maxRecDepth;
                v___x_5827_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15,
                );
                lean_inc_ref(v_inheritedTraceOptions_5821_);
                lean_inc(v_cancelTk_x3f_5819_);
                lean_inc(v_currMacroScope_5818_);
                lean_inc(v_quotContext_5817_);
                lean_inc(v_maxHeartbeats_5816_);
                lean_inc(v_initHeartbeats_5815_);
                lean_inc(v_openDecls_5814_);
                lean_inc(v_currNamespace_5813_);
                lean_inc(v_ref_5812_);
                lean_inc(v_currRecDepth_5811_);
                lean_inc_ref(v_fileMap_5810_);
                lean_inc_ref(v_fileName_5809_);
                if v_isShared_5824_ == 0 {
                    lean_ctor_set(v___x_5823_, 4, v___x_5827_);
                    lean_ctor_set(v___x_5823_, 2, v___x_5796_);
                    v___x_5829_ = v___x_5823_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_fileName_5809_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 1, v_fileMap_5810_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 2, v___x_5796_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 3, v_currRecDepth_5811_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 4, v___x_5827_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 5, v_ref_5812_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 6, v_currNamespace_5813_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 7, v_openDecls_5814_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 8, v_initHeartbeats_5815_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 9, v_maxHeartbeats_5816_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 10, v_quotContext_5817_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 11, v_currMacroScope_5818_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 12, v_cancelTk_x3f_5819_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 13, v_inheritedTraceOptions_5821_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5832_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_5820_,
                    );
                    v___x_5829_ = v_reuseFailAlloc_5832_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                lean_ctor_set_uint8(
                    v___x_5829_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_5804_,
                );
                v___x_5830_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(
                    v_options_5685_,
                    v___x_5803_,
                );
                v___x_5831_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5825_);
                lean_dec_ref(v_env_5825_);
                if v___x_5831_ == 0 {
                    if v___x_5830_ == 0 {
                        lean_dec_ref(v___x_5829_);
                        v___y_5701_ = v___x_5830_;
                        v___y_5702_ = v___x_5826_;
                        v_fileName_5703_ = v_fileName_5809_;
                        v_fileMap_5704_ = v_fileMap_5810_;
                        v_currRecDepth_5705_ = v_currRecDepth_5811_;
                        v_ref_5706_ = v_ref_5812_;
                        v_currNamespace_5707_ = v_currNamespace_5813_;
                        v_openDecls_5708_ = v_openDecls_5814_;
                        v_initHeartbeats_5709_ = v_initHeartbeats_5815_;
                        v_maxHeartbeats_5710_ = v_maxHeartbeats_5816_;
                        v_quotContext_5711_ = v_quotContext_5817_;
                        v_currMacroScope_5712_ = v_currMacroScope_5818_;
                        v_cancelTk_x3f_5713_ = v_cancelTk_x3f_5819_;
                        v_suppressElabErrors_5714_ = v_suppressElabErrors_5820_;
                        v_inheritedTraceOptions_5715_ = v_inheritedTraceOptions_5821_;
                        v___y_5716_ = v___y_5807_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_inheritedTraceOptions_5821_);
                        lean_dec(v_cancelTk_x3f_5819_);
                        lean_dec(v_currMacroScope_5818_);
                        lean_dec(v_quotContext_5817_);
                        lean_dec(v_maxHeartbeats_5816_);
                        lean_dec(v_initHeartbeats_5815_);
                        lean_dec(v_openDecls_5814_);
                        lean_dec(v_currNamespace_5813_);
                        lean_dec(v_ref_5812_);
                        lean_dec(v_currRecDepth_5811_);
                        lean_dec_ref(v_fileMap_5810_);
                        lean_dec_ref(v_fileName_5809_);
                        v___y_5767_ = v___x_5830_;
                        v___y_5768_ = v___x_5826_;
                        v___y_5769_ = v___y_5807_;
                        v___y_5770_ = v___x_5829_;
                        v___y_5771_ = v___x_5831_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inheritedTraceOptions_5821_);
                    lean_dec(v_cancelTk_x3f_5819_);
                    lean_dec(v_currMacroScope_5818_);
                    lean_dec(v_quotContext_5817_);
                    lean_dec(v_maxHeartbeats_5816_);
                    lean_dec(v_initHeartbeats_5815_);
                    lean_dec(v_openDecls_5814_);
                    lean_dec(v_currNamespace_5813_);
                    lean_dec(v_ref_5812_);
                    lean_dec(v_currRecDepth_5811_);
                    lean_dec_ref(v_fileMap_5810_);
                    lean_dec_ref(v_fileName_5809_);
                    v___y_5767_ = v___x_5830_;
                    v___y_5768_ = v___x_5826_;
                    v___y_5769_ = v___y_5807_;
                    v___y_5770_ = v___x_5829_;
                    v___y_5771_ = v___x_5830_;
                    state = 8;
                    continue;
                }
            }
            14 => {
                if v___y_5837_ == 0 {
                    v___x_5838_ = lean_st_ref_take(v___x_5699_);
                    v_env_5839_ = lean_ctor_get(v___x_5838_, 0);
                    v_nextMacroScope_5840_ = lean_ctor_get(v___x_5838_, 1);
                    v_ngen_5841_ = lean_ctor_get(v___x_5838_, 2);
                    v_auxDeclNGen_5842_ = lean_ctor_get(v___x_5838_, 3);
                    v_traceState_5843_ = lean_ctor_get(v___x_5838_, 4);
                    v_messages_5844_ = lean_ctor_get(v___x_5838_, 6);
                    v_infoState_5845_ = lean_ctor_get(v___x_5838_, 7);
                    v_snapshotTasks_5846_ = lean_ctor_get(v___x_5838_, 8);
                    v_isSharedCheck_5855_ = (!lean_is_exclusive(v___x_5838_)) as u8;
                    if v_isSharedCheck_5855_ == 0 {
                        v_unused_5856_ = lean_ctor_get(v___x_5838_, 5);
                        lean_dec(v_unused_5856_);
                        v___x_5848_ = v___x_5838_;
                        v_isShared_5849_ = v_isSharedCheck_5855_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_5846_);
                        lean_inc(v_infoState_5845_);
                        lean_inc(v_messages_5844_);
                        lean_inc(v_traceState_5843_);
                        lean_inc(v_auxDeclNGen_5842_);
                        lean_inc(v_ngen_5841_);
                        lean_inc(v_nextMacroScope_5840_);
                        lean_inc(v_env_5839_);
                        lean_dec(v___x_5838_);
                        v___x_5848_ = lean_box(0);
                        v_isShared_5849_ = v_isSharedCheck_5855_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_inc(v___x_5699_);
                    v___y_5806_ = v___x_5801_;
                    v___y_5807_ = v___x_5699_;
                    state = 11;
                    continue;
                }
            }
            15 => {
                v___x_5850_ = l_Lean_Kernel_enableDiag(v_env_5839_, v___x_5804_);
                if v_isShared_5849_ == 0 {
                    lean_ctor_set(v___x_5848_, 5, v___x_5680_);
                    lean_ctor_set(v___x_5848_, 0, v___x_5850_);
                    v___x_5852_ = v___x_5848_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 0, v___x_5850_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 1, v_nextMacroScope_5840_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 2, v_ngen_5841_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 3, v_auxDeclNGen_5842_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 4, v_traceState_5843_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 5, v___x_5680_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 6, v_messages_5844_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 7, v_infoState_5845_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 8, v_snapshotTasks_5846_);
                    v___x_5852_ = v_reuseFailAlloc_5854_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_5853_ = lean_st_ref_set(v___x_5699_, v___x_5852_);
                lean_inc(v___x_5699_);
                v___y_5806_ = v___x_5801_;
                v___y_5807_ = v___x_5699_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(
    mut v_info_5858_: *mut LeanObject,
    mut v_x_5859_: *mut LeanObject,
    mut v_a_5860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5861_: *mut LeanObject = core::ptr::null_mut();
    v_res_5861_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_5858_, v_x_5859_);
    return v_res_5861_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_runCoreM(
    mut v_00_u03b1_5862_: *mut LeanObject,
    mut v_info_5863_: *mut LeanObject,
    mut v_x_5864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    v___x_5866_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_5863_, v_x_5864_);
    return v___x_5866_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_runCoreM___boxed(
    mut v_00_u03b1_5867_: *mut LeanObject,
    mut v_info_5868_: *mut LeanObject,
    mut v_x_5869_: *mut LeanObject,
    mut v_a_5870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5871_: *mut LeanObject = core::ptr::null_mut();
    v_res_5871_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_5867_, v_info_5868_, v_x_5869_);
    return v_res_5871_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(
    mut v___x_5872_: *mut LeanObject,
    mut v_x_5873_: *mut LeanObject,
    mut v___x_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v_a_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5893_: u8 = 0;
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5878_ = lean_st_mk_ref(v___x_5872_);
                lean_inc(v___x_5878_);
                v___x_5879_ = lean_apply_5(
                    v_x_5873_,
                    v___x_5874_,
                    v___x_5878_,
                    v___y_5875_,
                    v___y_5876_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5879_) == 0 {
                    v_a_5880_ = lean_ctor_get(v___x_5879_, 0);
                    v_isSharedCheck_5889_ = (!lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5889_ == 0 {
                        v___x_5882_ = v___x_5879_;
                        v_isShared_5883_ = v_isSharedCheck_5889_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5880_);
                        lean_dec(v___x_5879_);
                        v___x_5882_ = lean_box(0);
                        v_isShared_5883_ = v_isSharedCheck_5889_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5878_);
                    v_a_5890_ = lean_ctor_get(v___x_5879_, 0);
                    v_isSharedCheck_5897_ = (!lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5897_ == 0 {
                        v___x_5892_ = v___x_5879_;
                        v_isShared_5893_ = v_isSharedCheck_5897_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5890_);
                        lean_dec(v___x_5879_);
                        v___x_5892_ = lean_box(0);
                        v_isShared_5893_ = v_isSharedCheck_5897_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5884_ = lean_st_ref_get(v___x_5878_);
                lean_dec(v___x_5878_);
                v___x_5885_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5885_, 0, v_a_5880_);
                lean_ctor_set(v___x_5885_, 1, v___x_5884_);
                if v_isShared_5883_ == 0 {
                    lean_ctor_set(v___x_5882_, 0, v___x_5885_);
                    v___x_5887_ = v___x_5882_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5888_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5888_, 0, v___x_5885_);
                    v___x_5887_ = v_reuseFailAlloc_5888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5887_;
            }
            3 => {
                if v_isShared_5893_ == 0 {
                    v___x_5895_ = v___x_5892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_a_5890_);
                    v___x_5895_ = v_reuseFailAlloc_5896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(
    mut v___x_5898_: *mut LeanObject,
    mut v_x_5899_: *mut LeanObject,
    mut v___x_5900_: *mut LeanObject,
    mut v___y_5901_: *mut LeanObject,
    mut v___y_5902_: *mut LeanObject,
    mut v___y_5903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5904_: *mut LeanObject = core::ptr::null_mut();
    v_res_5904_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(
        v___x_5898_,
        v_x_5899_,
        v___x_5900_,
        v___y_5901_,
        v___y_5902_,
    );
    return v_res_5904_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1() -> u64 {
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: u64 = 0;
    v___x_5911_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0;
    v___x_5912_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5911_);
    return v___x_5912_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_5913_: u64 = 0;
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    v___x_5913_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once),
        _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1,
    );
    v___x_5914_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0;
    v___x_5915_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_5915_, 0, v___x_5914_);
    lean_ctor_set_uint64(
        v___x_5915_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5913_,
    );
    return v___x_5915_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    v___x_5918_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5918_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut LeanObject = core::ptr::null_mut();
    v___x_5919_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once),
        _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4,
    );
    v___x_5920_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5920_, 0, v___x_5919_);
    return v___x_5920_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    v___x_5921_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once),
        _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5,
    );
    v___x_5922_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5922_, 0, v___x_5921_);
    lean_ctor_set(v___x_5922_, 1, v___x_5921_);
    lean_ctor_set(v___x_5922_, 2, v___x_5921_);
    lean_ctor_set(v___x_5922_, 3, v___x_5921_);
    lean_ctor_set(v___x_5922_, 4, v___x_5921_);
    lean_ctor_set(v___x_5922_, 5, v___x_5921_);
    return v___x_5922_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    v___x_5923_ = lean_unsigned_to_nat(32);
    v___x_5924_ = lean_mk_empty_array_with_capacity(v___x_5923_);
    v___x_5925_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5925_, 0, v___x_5924_);
    return v___x_5925_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_5926_: usize = 0;
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    v___x_5926_ = 5usize;
    v___x_5927_ = lean_unsigned_to_nat(0);
    v___x_5928_ = lean_unsigned_to_nat(32);
    v___x_5929_ = lean_mk_empty_array_with_capacity(v___x_5928_);
    v___x_5930_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once),
        _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7,
    );
    v___x_5931_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5931_, 0, v___x_5930_);
    lean_ctor_set(v___x_5931_, 1, v___x_5929_);
    lean_ctor_set(v___x_5931_, 2, v___x_5927_);
    lean_ctor_set(v___x_5931_, 3, v___x_5927_);
    lean_ctor_set_usize(v___x_5931_, 4, v___x_5926_);
    return v___x_5931_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    v___x_5932_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once),
        _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5,
    );
    v___x_5933_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_5933_, 0, v___x_5932_);
    lean_ctor_set(v___x_5933_, 1, v___x_5932_);
    lean_ctor_set(v___x_5933_, 2, v___x_5932_);
    lean_ctor_set(v___x_5933_, 3, v___x_5932_);
    lean_ctor_set(v___x_5933_, 4, v___x_5932_);
    return v___x_5933_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_runMetaM___redArg(
    mut v_info_5934_: *mut LeanObject,
    mut v_lctx_5935_: *mut LeanObject,
    mut v_x_5936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: u8 = 0;
    let mut v___x_5940_: u8 = 0;
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5957_: u8 = 0;
    let mut v_fst_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut v_a_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5966_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5938_ = lean_box(1);
                v___x_5939_ = 0;
                v___x_5940_ = 1;
                v___x_5941_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2,
                );
                v___x_5942_ = lean_unsigned_to_nat(0);
                v___x_5943_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3;
                v___x_5944_ = lean_box(0);
                v___x_5945_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5945_, 0, v___x_5941_);
                lean_ctor_set(v___x_5945_, 1, v___x_5938_);
                lean_ctor_set(v___x_5945_, 2, v_lctx_5935_);
                lean_ctor_set(v___x_5945_, 3, v___x_5943_);
                lean_ctor_set(v___x_5945_, 4, v___x_5944_);
                lean_ctor_set(v___x_5945_, 5, v___x_5942_);
                lean_ctor_set(v___x_5945_, 6, v___x_5944_);
                lean_ctor_set_uint8(
                    v___x_5945_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_5939_,
                );
                lean_ctor_set_uint8(
                    v___x_5945_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_5939_,
                );
                lean_ctor_set_uint8(
                    v___x_5945_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_5939_,
                );
                lean_ctor_set_uint8(
                    v___x_5945_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_5940_,
                );
                v_toCommandContextInfo_5946_ = lean_ctor_get(v_info_5934_, 0);
                v_mctx_5947_ = lean_ctor_get(v_toCommandContextInfo_5946_, 3);
                v___x_5948_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6,
                );
                v___x_5949_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8,
                );
                v___x_5950_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once
                    ),
                    _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9,
                );
                lean_inc_ref(v_mctx_5947_);
                v___x_5951_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5951_, 0, v_mctx_5947_);
                lean_ctor_set(v___x_5951_, 1, v___x_5948_);
                lean_ctor_set(v___x_5951_, 2, v___x_5938_);
                lean_ctor_set(v___x_5951_, 3, v___x_5949_);
                lean_ctor_set(v___x_5951_, 4, v___x_5950_);
                v___f_5952_ = lean_alloc_closure(
                    l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_5952_, 0, v___x_5951_);
                lean_closure_set(v___f_5952_, 1, v_x_5936_);
                lean_closure_set(v___f_5952_, 2, v___x_5945_);
                v___x_5953_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_5934_, v___f_5952_);
                if lean_obj_tag(v___x_5953_) == 0 {
                    v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_5962_ = (!lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_5962_ == 0 {
                        v___x_5956_ = v___x_5953_;
                        v_isShared_5957_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5954_);
                        lean_dec(v___x_5953_);
                        v___x_5956_ = lean_box(0);
                        v_isShared_5957_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5963_ = lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_5970_ = (!lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_5970_ == 0 {
                        v___x_5965_ = v___x_5953_;
                        v_isShared_5966_ = v_isSharedCheck_5970_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5963_);
                        lean_dec(v___x_5953_);
                        v___x_5965_ = lean_box(0);
                        v_isShared_5966_ = v_isSharedCheck_5970_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5958_ = lean_ctor_get(v_a_5954_, 0);
                lean_inc(v_fst_5958_);
                lean_dec(v_a_5954_);
                if v_isShared_5957_ == 0 {
                    lean_ctor_set(v___x_5956_, 0, v_fst_5958_);
                    v___x_5960_ = v___x_5956_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_fst_5958_);
                    v___x_5960_ = v_reuseFailAlloc_5961_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5960_;
            }
            3 => {
                if v_isShared_5966_ == 0 {
                    v___x_5968_ = v___x_5965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
                    v___x_5968_ = v_reuseFailAlloc_5969_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(
    mut v_info_5971_: *mut LeanObject,
    mut v_lctx_5972_: *mut LeanObject,
    mut v_x_5973_: *mut LeanObject,
    mut v_a_5974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5975_: *mut LeanObject = core::ptr::null_mut();
    v_res_5975_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_5971_, v_lctx_5972_, v_x_5973_);
    return v_res_5975_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_runMetaM(
    mut v_00_u03b1_5976_: *mut LeanObject,
    mut v_info_5977_: *mut LeanObject,
    mut v_lctx_5978_: *mut LeanObject,
    mut v_x_5979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    v___x_5981_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_5977_, v_lctx_5978_, v_x_5979_);
    return v___x_5981_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_runMetaM___boxed(
    mut v_00_u03b1_5982_: *mut LeanObject,
    mut v_info_5983_: *mut LeanObject,
    mut v_lctx_5984_: *mut LeanObject,
    mut v_x_5985_: *mut LeanObject,
    mut v_a_5986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5987_: *mut LeanObject = core::ptr::null_mut();
    v_res_5987_ =
        l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_5982_, v_info_5983_, v_lctx_5984_, v_x_5985_);
    return v_res_5987_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_toPPContext(
    mut v_info_5988_: *mut LeanObject,
    mut v_lctx_5989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toCommandContextInfo_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    v_toCommandContextInfo_5990_ = lean_ctor_get(v_info_5988_, 0);
    v_env_5991_ = lean_ctor_get(v_toCommandContextInfo_5990_, 0);
    v_mctx_5992_ = lean_ctor_get(v_toCommandContextInfo_5990_, 3);
    v_options_5993_ = lean_ctor_get(v_toCommandContextInfo_5990_, 4);
    v_currNamespace_5994_ = lean_ctor_get(v_toCommandContextInfo_5990_, 5);
    v_openDecls_5995_ = lean_ctor_get(v_toCommandContextInfo_5990_, 6);
    lean_inc(v_openDecls_5995_);
    lean_inc(v_currNamespace_5994_);
    lean_inc_ref(v_options_5993_);
    lean_inc_ref(v_mctx_5992_);
    lean_inc_ref(v_env_5991_);
    v___x_5996_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5996_, 0, v_env_5991_);
    lean_ctor_set(v___x_5996_, 1, v_mctx_5992_);
    lean_ctor_set(v___x_5996_, 2, v_lctx_5989_);
    lean_ctor_set(v___x_5996_, 3, v_options_5993_);
    lean_ctor_set(v___x_5996_, 4, v_currNamespace_5994_);
    lean_ctor_set(v___x_5996_, 5, v_openDecls_5995_);
    return v___x_5996_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_toPPContext___boxed(
    mut v_info_5997_: *mut LeanObject,
    mut v_lctx_5998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5999_: *mut LeanObject = core::ptr::null_mut();
    v_res_5999_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_5997_, v_lctx_5998_);
    lean_dec_ref(v_info_5997_);
    return v_res_5999_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_ppSyntax(
    mut v_info_6000_: *mut LeanObject,
    mut v_lctx_6001_: *mut LeanObject,
    mut v_stx_6002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    v___x_6004_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_6000_, v_lctx_6001_);
    v___x_6005_ = l_Lean_ppTerm(v___x_6004_, v_stx_6002_);
    v___x_6006_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6006_, 0, v___x_6005_);
    return v___x_6006_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_ppSyntax___boxed(
    mut v_info_6007_: *mut LeanObject,
    mut v_lctx_6008_: *mut LeanObject,
    mut v_stx_6009_: *mut LeanObject,
    mut v_a_6010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6011_: *mut LeanObject = core::ptr::null_mut();
    v_res_6011_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_6007_, v_lctx_6008_, v_stx_6009_);
    lean_dec_ref(v_info_6007_);
    return v_res_6011_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(
    mut v_ctx_6027_: *mut LeanObject,
    mut v_pos_6028_: *mut LeanObject,
    mut v_info_6029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toCommandContextInfo_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6037_: u8 = 0;
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonical_6053_: u8 = 0;
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toCommandContextInfo_6030_ = lean_ctor_get(v_ctx_6027_, 0);
                lean_inc_ref(v_toCommandContextInfo_6030_);
                lean_dec_ref(v_ctx_6027_);
                v_fileMap_6031_ = lean_ctor_get(v_toCommandContextInfo_6030_, 2);
                lean_inc_ref(v_fileMap_6031_);
                lean_dec_ref(v_toCommandContextInfo_6030_);
                v___x_6032_ = l_Lean_FileMap_toPosition(v_fileMap_6031_, v_pos_6028_);
                v_line_6033_ = lean_ctor_get(v___x_6032_, 0);
                v_column_6034_ = lean_ctor_get(v___x_6032_, 1);
                v_isSharedCheck_6057_ = (!lean_is_exclusive(v___x_6032_)) as u8;
                if v_isSharedCheck_6057_ == 0 {
                    v___x_6036_ = v___x_6032_;
                    v_isShared_6037_ = v_isSharedCheck_6057_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_column_6034_);
                    lean_inc(v_line_6033_);
                    lean_dec(v___x_6032_);
                    v___x_6036_ = lean_box(0);
                    v_isShared_6037_ = v_isSharedCheck_6057_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6038_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1;
                v___x_6039_ = l_Nat_reprFast(v_line_6033_);
                v___x_6040_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6040_, 0, v___x_6039_);
                if v_isShared_6037_ == 0 {
                    lean_ctor_set_tag(v___x_6036_, 5);
                    lean_ctor_set(v___x_6036_, 1, v___x_6040_);
                    lean_ctor_set(v___x_6036_, 0, v___x_6038_);
                    v___x_6042_ = v___x_6036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6056_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6056_, 0, v___x_6038_);
                    lean_ctor_set(v_reuseFailAlloc_6056_, 1, v___x_6040_);
                    v___x_6042_ = v_reuseFailAlloc_6056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6043_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3;
                v___x_6044_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6044_, 0, v___x_6042_);
                lean_ctor_set(v___x_6044_, 1, v___x_6043_);
                v___x_6045_ = l_Nat_reprFast(v_column_6034_);
                v___x_6046_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6046_, 0, v___x_6045_);
                v___x_6047_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6047_, 0, v___x_6044_);
                lean_ctor_set(v___x_6047_, 1, v___x_6046_);
                v___x_6048_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5;
                v_pos_6049_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v_pos_6049_, 0, v___x_6047_);
                lean_ctor_set(v_pos_6049_, 1, v___x_6048_);
                match lean_obj_tag(v_info_6029_) {
                    0 => {
                        return v_pos_6049_;
                    }
                    1 => {
                        v_canonical_6053_ = lean_ctor_get_uint8(
                            v_info_6029_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        if v_canonical_6053_ == 1 {
                            v___x_6054_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9;
                            v___x_6055_ = lean_alloc_ctor(5, 2, (0) as u32);
                            lean_ctor_set(v___x_6055_, 0, v_pos_6049_);
                            lean_ctor_set(v___x_6055_, 1, v___x_6054_);
                            return v___x_6055_;
                        } else {
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6051_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7;
                v___x_6052_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6052_, 0, v_pos_6049_);
                lean_ctor_set(v___x_6052_, 1, v___x_6051_);
                return v___x_6052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(
    mut v_ctx_6058_: *mut LeanObject,
    mut v_pos_6059_: *mut LeanObject,
    mut v_info_6060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6061_: *mut LeanObject = core::ptr::null_mut();
    v_res_6061_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(
        v_ctx_6058_,
        v_pos_6059_,
        v_info_6060_,
    );
    lean_dec(v_info_6060_);
    lean_dec(v_pos_6059_);
    return v_res_6061_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(
    mut v_ctx_6065_: *mut LeanObject,
    mut v_stx_6066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: u8 = 0;
    let mut v___y_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6077_ = 0;
                v___x_6082_ = l_Lean_Syntax_getPos_x3f(v_stx_6066_, v___x_6077_);
                if lean_obj_tag(v___x_6082_) == 0 {
                    v___x_6083_ = lean_unsigned_to_nat(0);
                    v___y_6079_ = v___x_6083_;
                    state = 2;
                    continue;
                } else {
                    v_val_6084_ = lean_ctor_get(v___x_6082_, 0);
                    lean_inc(v_val_6084_);
                    lean_dec_ref_known(v___x_6082_, 1);
                    v___y_6079_ = v_val_6084_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6070_ = l_Lean_Syntax_getHeadInfo(v_stx_6066_);
                lean_inc_ref(v_ctx_6065_);
                v___x_6071_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(
                        v_ctx_6065_,
                        v___y_6068_,
                        v___x_6070_,
                    );
                lean_dec(v___x_6070_);
                lean_dec(v___y_6068_);
                v___x_6072_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1;
                v___x_6073_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6073_, 0, v___x_6071_);
                lean_ctor_set(v___x_6073_, 1, v___x_6072_);
                v___x_6074_ = l_Lean_Syntax_getTailInfo(v_stx_6066_);
                v___x_6075_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(
                        v_ctx_6065_,
                        v___y_6069_,
                        v___x_6074_,
                    );
                lean_dec(v___x_6074_);
                lean_dec(v___y_6069_);
                v___x_6076_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6076_, 0, v___x_6073_);
                lean_ctor_set(v___x_6076_, 1, v___x_6075_);
                return v___x_6076_;
            }
            2 => {
                v___x_6080_ = l_Lean_Syntax_getTailPos_x3f(v_stx_6066_, v___x_6077_);
                if lean_obj_tag(v___x_6080_) == 0 {
                    lean_inc(v___y_6079_);
                    v___y_6068_ = v___y_6079_;
                    v___y_6069_ = v___y_6079_;
                    state = 1;
                    continue;
                } else {
                    v_val_6081_ = lean_ctor_get(v___x_6080_, 0);
                    lean_inc(v_val_6081_);
                    lean_dec_ref_known(v___x_6080_, 1);
                    v___y_6068_ = v___y_6079_;
                    v___y_6069_ = v_val_6081_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(
    mut v_ctx_6085_: *mut LeanObject,
    mut v_stx_6086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6087_: *mut LeanObject = core::ptr::null_mut();
    v_res_6087_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_6085_, v_stx_6086_);
    lean_dec(v_stx_6086_);
    return v_res_6087_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(
    mut v_ctx_6091_: *mut LeanObject,
    mut v_info_6092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elaborator_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6097_: u8 = 0;
    let mut v___x_6098_: u8 = 0;
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: u8 = 0;
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elaborator_6093_ = lean_ctor_get(v_info_6092_, 0);
                v_stx_6094_ = lean_ctor_get(v_info_6092_, 1);
                v_isSharedCheck_6109_ = (!lean_is_exclusive(v_info_6092_)) as u8;
                if v_isSharedCheck_6109_ == 0 {
                    v___x_6096_ = v_info_6092_;
                    v_isShared_6097_ = v_isSharedCheck_6109_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stx_6094_);
                    lean_inc(v_elaborator_6093_);
                    lean_dec(v_info_6092_);
                    v___x_6096_ = lean_box(0);
                    v_isShared_6097_ = v_isSharedCheck_6109_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6098_ = l_Lean_Name_isAnonymous(v_elaborator_6093_);
                if v___x_6098_ == 0 {
                    v___x_6099_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(
                        v_ctx_6091_,
                        v_stx_6094_,
                    );
                    lean_dec(v_stx_6094_);
                    v___x_6100_ =
                        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
                    if v_isShared_6097_ == 0 {
                        lean_ctor_set_tag(v___x_6096_, 5);
                        lean_ctor_set(v___x_6096_, 1, v___x_6100_);
                        lean_ctor_set(v___x_6096_, 0, v___x_6099_);
                        v___x_6102_ = v___x_6096_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6107_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6107_, 0, v___x_6099_);
                        lean_ctor_set(v_reuseFailAlloc_6107_, 1, v___x_6100_);
                        v___x_6102_ = v_reuseFailAlloc_6107_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6096_);
                    lean_dec(v_elaborator_6093_);
                    v___x_6108_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(
                        v_ctx_6091_,
                        v_stx_6094_,
                    );
                    lean_dec(v_stx_6094_);
                    return v___x_6108_;
                }
            }
            2 => {
                v___x_6103_ = 1;
                v___x_6104_ = l_Lean_Name_toString(v_elaborator_6093_, v___x_6103_);
                v___x_6105_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6105_, 0, v___x_6104_);
                v___x_6106_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6106_, 0, v___x_6102_);
                lean_ctor_set(v___x_6106_, 1, v___x_6105_);
                return v___x_6106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TermInfo_runMetaM___redArg(
    mut v_info_6110_: *mut LeanObject,
    mut v_ctx_6111_: *mut LeanObject,
    mut v_x_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_6114_ = lean_ctor_get(v_info_6110_, 1);
    lean_inc_ref(v_lctx_6114_);
    lean_dec_ref(v_info_6110_);
    v___x_6115_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6111_, v_lctx_6114_, v_x_6112_);
    return v___x_6115_;
}
pub unsafe fn l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(
    mut v_info_6116_: *mut LeanObject,
    mut v_ctx_6117_: *mut LeanObject,
    mut v_x_6118_: *mut LeanObject,
    mut v_a_6119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6120_: *mut LeanObject = core::ptr::null_mut();
    v_res_6120_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_6116_, v_ctx_6117_, v_x_6118_);
    return v_res_6120_;
}
pub unsafe fn l_Lean_Elab_TermInfo_runMetaM(
    mut v_00_u03b1_6121_: *mut LeanObject,
    mut v_info_6122_: *mut LeanObject,
    mut v_ctx_6123_: *mut LeanObject,
    mut v_x_6124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    v___x_6126_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_6122_, v_ctx_6123_, v_x_6124_);
    return v___x_6126_;
}
pub unsafe fn l_Lean_Elab_TermInfo_runMetaM___boxed(
    mut v_00_u03b1_6127_: *mut LeanObject,
    mut v_info_6128_: *mut LeanObject,
    mut v_ctx_6129_: *mut LeanObject,
    mut v_x_6130_: *mut LeanObject,
    mut v_a_6131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6132_: *mut LeanObject = core::ptr::null_mut();
    v_res_6132_ =
        l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_6127_, v_info_6128_, v_ctx_6129_, v_x_6130_);
    return v_res_6132_;
}
pub unsafe fn l_Lean_Elab_TermInfo_format___lam__0(
    mut v_ctx_6147_: *mut LeanObject,
    mut v_toElabInfo_6148_: *mut LeanObject,
    mut v_expr_6149_: *mut LeanObject,
    mut v_isBinder_6150_: u8,
    mut v___y_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6182_: u8 = 0;
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: u8 = 0;
    let mut v___x_6188_: u8 = 0;
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6197_: u8 = 0;
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6154_);
                lean_inc_ref(v___y_6153_);
                lean_inc(v___y_6152_);
                lean_inc_ref(v___y_6151_);
                lean_inc_ref(v_expr_6149_);
                v___x_6189_ = lean_infer_type(
                    v_expr_6149_,
                    v___y_6151_,
                    v___y_6152_,
                    v___y_6153_,
                    v___y_6154_,
                );
                if lean_obj_tag(v___x_6189_) == 0 {
                    v_a_6190_ = lean_ctor_get(v___x_6189_, 0);
                    lean_inc(v_a_6190_);
                    lean_dec_ref_known(v___x_6189_, 1);
                    v___x_6191_ = l_Lean_Meta_ppExpr(
                        v_a_6190_,
                        v___y_6151_,
                        v___y_6152_,
                        v___y_6153_,
                        v___y_6154_,
                    );
                    if lean_obj_tag(v___x_6191_) == 0 {
                        v_a_6192_ = lean_ctor_get(v___x_6191_, 0);
                        lean_inc(v_a_6192_);
                        lean_dec_ref_known(v___x_6191_, 1);
                        v_a_6171_ = v_a_6192_;
                        state = 2;
                        continue;
                    } else {
                        v_a_6193_ = lean_ctor_get(v___x_6191_, 0);
                        lean_inc(v_a_6193_);
                        v___y_6185_ = v___x_6191_;
                        v_a_6186_ = v_a_6193_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6194_ = lean_ctor_get(v___x_6189_, 0);
                    v_isSharedCheck_6201_ = (!lean_is_exclusive(v___x_6189_)) as u8;
                    if v_isSharedCheck_6201_ == 0 {
                        v___x_6196_ = v___x_6189_;
                        v_isShared_6197_ = v_isSharedCheck_6201_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6194_);
                        lean_dec(v___x_6189_);
                        v___x_6196_ = lean_box(0);
                        v_isShared_6197_ = v_isSharedCheck_6201_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_6159_);
                v___x_6160_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6160_, 0, v___y_6159_);
                v___x_6161_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6161_, 0, v___y_6157_);
                lean_ctor_set(v___x_6161_, 1, v___x_6160_);
                v___x_6162_ = l_Lean_Elab_TermInfo_format___lam__0___closed__1;
                v___x_6163_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6163_, 0, v___x_6161_);
                lean_ctor_set(v___x_6163_, 1, v___x_6162_);
                v___x_6164_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6164_, 0, v___x_6163_);
                lean_ctor_set(v___x_6164_, 1, v___y_6158_);
                v___x_6165_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
                v___x_6166_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6166_, 0, v___x_6164_);
                lean_ctor_set(v___x_6166_, 1, v___x_6165_);
                v___x_6167_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(
                    v_ctx_6147_,
                    v_toElabInfo_6148_,
                );
                v___x_6168_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6168_, 0, v___x_6166_);
                lean_ctor_set(v___x_6168_, 1, v___x_6167_);
                v___x_6169_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6169_, 0, v___x_6168_);
                return v___x_6169_;
            }
            2 => {
                v___x_6172_ = l_Lean_Meta_ppExpr(
                    v_expr_6149_,
                    v___y_6151_,
                    v___y_6152_,
                    v___y_6153_,
                    v___y_6154_,
                );
                lean_dec(v___y_6154_);
                lean_dec_ref(v___y_6153_);
                lean_dec(v___y_6152_);
                lean_dec_ref(v___y_6151_);
                if lean_obj_tag(v___x_6172_) == 0 {
                    v_a_6173_ = lean_ctor_get(v___x_6172_, 0);
                    lean_inc(v_a_6173_);
                    lean_dec_ref_known(v___x_6172_, 1);
                    v___x_6174_ = l_Lean_Elab_TermInfo_format___lam__0___closed__3;
                    v___x_6175_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6175_, 0, v___x_6174_);
                    lean_ctor_set(v___x_6175_, 1, v_a_6173_);
                    v___x_6176_ = l_Lean_Elab_TermInfo_format___lam__0___closed__5;
                    v___x_6177_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6177_, 0, v___x_6175_);
                    lean_ctor_set(v___x_6177_, 1, v___x_6176_);
                    if v_isBinder_6150_ == 0 {
                        v___x_6178_ = l_Lean_Elab_TermInfo_format___lam__0___closed__6;
                        v___y_6157_ = v___x_6177_;
                        v___y_6158_ = v_a_6171_;
                        v___y_6159_ = v___x_6178_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6179_ = l_Lean_Elab_TermInfo_format___lam__0___closed__7;
                        v___y_6157_ = v___x_6177_;
                        v___y_6158_ = v_a_6171_;
                        v___y_6159_ = v___x_6179_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6171_);
                    lean_dec_ref(v_toElabInfo_6148_);
                    lean_dec_ref(v_ctx_6147_);
                    return v___x_6172_;
                }
            }
            3 => {
                if v___y_6182_ == 0 {
                    lean_dec_ref(v___y_6181_);
                    v___x_6183_ = l_Lean_Elab_TermInfo_format___lam__0___closed__9;
                    v_a_6171_ = v___x_6183_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_6154_);
                    lean_dec_ref(v___y_6153_);
                    lean_dec(v___y_6152_);
                    lean_dec_ref(v___y_6151_);
                    lean_dec_ref(v_expr_6149_);
                    lean_dec_ref(v_toElabInfo_6148_);
                    lean_dec_ref(v_ctx_6147_);
                    return v___y_6181_;
                }
            }
            4 => {
                v___x_6187_ = l_Lean_Exception_isInterrupt(v_a_6186_);
                if v___x_6187_ == 0 {
                    v___x_6188_ = l_Lean_Exception_isRuntime(v_a_6186_);
                    v___y_6181_ = v___y_6185_;
                    v___y_6182_ = v___x_6188_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v_a_6186_);
                    v___y_6181_ = v___y_6185_;
                    v___y_6182_ = v___x_6187_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                lean_inc(v_a_6194_);
                if v_isShared_6197_ == 0 {
                    v___x_6199_ = v___x_6196_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6200_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6200_, 0, v_a_6194_);
                    v___x_6199_ = v_reuseFailAlloc_6200_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_6185_ = v___x_6199_;
                v_a_6186_ = v_a_6194_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TermInfo_format___lam__0___boxed(
    mut v_ctx_6202_: *mut LeanObject,
    mut v_toElabInfo_6203_: *mut LeanObject,
    mut v_expr_6204_: *mut LeanObject,
    mut v_isBinder_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
    mut v___y_6207_: *mut LeanObject,
    mut v___y_6208_: *mut LeanObject,
    mut v___y_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isBinder_boxed_6211_: u8 = 0;
    let mut v_res_6212_: *mut LeanObject = core::ptr::null_mut();
    v_isBinder_boxed_6211_ = (lean_unbox(v_isBinder_6205_) as u8);
    v_res_6212_ = l_Lean_Elab_TermInfo_format___lam__0(
        v_ctx_6202_,
        v_toElabInfo_6203_,
        v_expr_6204_,
        v_isBinder_boxed_6211_,
        v___y_6206_,
        v___y_6207_,
        v___y_6208_,
        v___y_6209_,
    );
    return v_res_6212_;
}
pub unsafe fn l_Lean_Elab_TermInfo_format(
    mut v_ctx_6213_: *mut LeanObject,
    mut v_info_6214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toElabInfo_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isBinder_6218_: u8 = 0;
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    v_toElabInfo_6216_ = lean_ctor_get(v_info_6214_, 0);
    v_expr_6217_ = lean_ctor_get(v_info_6214_, 3);
    v_isBinder_6218_ = lean_ctor_get_uint8(
        v_info_6214_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
    );
    v___x_6219_ = lean_box((v_isBinder_6218_) as usize);
    lean_inc_ref(v_expr_6217_);
    lean_inc_ref(v_toElabInfo_6216_);
    lean_inc_ref(v_ctx_6213_);
    v___f_6220_ = lean_alloc_closure(
        l_Lean_Elab_TermInfo_format___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_6220_, 0, v_ctx_6213_);
    lean_closure_set(v___f_6220_, 1, v_toElabInfo_6216_);
    lean_closure_set(v___f_6220_, 2, v_expr_6217_);
    lean_closure_set(v___f_6220_, 3, v___x_6219_);
    v___x_6221_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_6214_, v_ctx_6213_, v___f_6220_);
    return v___x_6221_;
}
pub unsafe fn l_Lean_Elab_TermInfo_format___boxed(
    mut v_ctx_6222_: *mut LeanObject,
    mut v_info_6223_: *mut LeanObject,
    mut v_a_6224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6225_: *mut LeanObject = core::ptr::null_mut();
    v_res_6225_ = l_Lean_Elab_TermInfo_format(v_ctx_6222_, v_info_6223_);
    return v_res_6225_;
}
pub unsafe fn l_Lean_Elab_PartialTermInfo_format(
    mut v_ctx_6229_: *mut LeanObject,
    mut v_info_6230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toElabInfo_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    v_toElabInfo_6231_ = lean_ctor_get(v_info_6230_, 0);
    lean_inc_ref(v_toElabInfo_6231_);
    lean_dec_ref(v_info_6230_);
    v___x_6232_ = l_Lean_Elab_PartialTermInfo_format___closed__1;
    v___x_6233_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(
        v_ctx_6229_,
        v_toElabInfo_6231_,
    );
    v___x_6234_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6234_, 0, v___x_6232_);
    lean_ctor_set(v___x_6234_, 1, v___x_6233_);
    return v___x_6234_;
}
pub unsafe fn l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(
    mut v_x_6241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6246_: u8 = 0;
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6241_) == 0 {
                    v___x_6242_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1;
                    return v___x_6242_;
                } else {
                    v_val_6243_ = lean_ctor_get(v_x_6241_, 0);
                    v_isSharedCheck_6253_ = (!lean_is_exclusive(v_x_6241_)) as u8;
                    if v_isSharedCheck_6253_ == 0 {
                        v___x_6245_ = v_x_6241_;
                        v_isShared_6246_ = v_isSharedCheck_6253_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6243_);
                        lean_dec(v_x_6241_);
                        v___x_6245_ = lean_box(0);
                        v_isShared_6246_ = v_isSharedCheck_6253_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6247_ =
                    l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3;
                v___x_6248_ = lean_expr_dbg_to_string(v_val_6243_);
                lean_dec(v_val_6243_);
                if v_isShared_6246_ == 0 {
                    lean_ctor_set_tag(v___x_6245_, 3);
                    lean_ctor_set(v___x_6245_, 0, v___x_6248_);
                    v___x_6250_ = v___x_6245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6252_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6252_, 0, v___x_6248_);
                    v___x_6250_ = v_reuseFailAlloc_6252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6251_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6251_, 0, v___x_6247_);
                lean_ctor_set(v___x_6251_, 1, v___x_6250_);
                return v___x_6251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_format___lam__0(
    mut v_ctx_6260_: *mut LeanObject,
    mut v_lctx_6261_: *mut LeanObject,
    mut v_stx_6262_: *mut LeanObject,
    mut v_expectedType_x3f_6263_: *mut LeanObject,
    mut v_info_6264_: *mut LeanObject,
    mut v___y_6265_: *mut LeanObject,
    mut v___y_6266_: *mut LeanObject,
    mut v___y_6267_: *mut LeanObject,
    mut v___y_6268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6274_: u8 = 0;
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6270_ =
                    l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_6260_, v_lctx_6261_, v_stx_6262_);
                v_a_6271_ = lean_ctor_get(v___x_6270_, 0);
                v_isSharedCheck_6289_ = (!lean_is_exclusive(v___x_6270_)) as u8;
                if v_isSharedCheck_6289_ == 0 {
                    v___x_6273_ = v___x_6270_;
                    v_isShared_6274_ = v_isSharedCheck_6289_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6271_);
                    lean_dec(v___x_6270_);
                    v___x_6273_ = lean_box(0);
                    v_isShared_6274_ = v_isSharedCheck_6289_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6275_ = l_Lean_Elab_CompletionInfo_format___lam__0___closed__1;
                v___x_6276_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6276_, 0, v___x_6275_);
                lean_ctor_set(v___x_6276_, 1, v_a_6271_);
                v___x_6277_ = l_Lean_Elab_CompletionInfo_format___lam__0___closed__3;
                v___x_6278_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6278_, 0, v___x_6276_);
                lean_ctor_set(v___x_6278_, 1, v___x_6277_);
                v___x_6279_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(
                    v_expectedType_x3f_6263_,
                );
                v___x_6280_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6280_, 0, v___x_6278_);
                lean_ctor_set(v___x_6280_, 1, v___x_6279_);
                v___x_6281_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
                v___x_6282_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6282_, 0, v___x_6280_);
                lean_ctor_set(v___x_6282_, 1, v___x_6281_);
                v___x_6283_ = l_Lean_Elab_CompletionInfo_stx(v_info_6264_);
                v___x_6284_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(
                    v_ctx_6260_,
                    v___x_6283_,
                );
                lean_dec(v___x_6283_);
                v___x_6285_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6285_, 0, v___x_6282_);
                lean_ctor_set(v___x_6285_, 1, v___x_6284_);
                if v_isShared_6274_ == 0 {
                    lean_ctor_set(v___x_6273_, 0, v___x_6285_);
                    v___x_6287_ = v___x_6273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6288_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6288_, 0, v___x_6285_);
                    v___x_6287_ = v_reuseFailAlloc_6288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_format___lam__0___boxed(
    mut v_ctx_6290_: *mut LeanObject,
    mut v_lctx_6291_: *mut LeanObject,
    mut v_stx_6292_: *mut LeanObject,
    mut v_expectedType_x3f_6293_: *mut LeanObject,
    mut v_info_6294_: *mut LeanObject,
    mut v___y_6295_: *mut LeanObject,
    mut v___y_6296_: *mut LeanObject,
    mut v___y_6297_: *mut LeanObject,
    mut v___y_6298_: *mut LeanObject,
    mut v___y_6299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6300_: *mut LeanObject = core::ptr::null_mut();
    v_res_6300_ = l_Lean_Elab_CompletionInfo_format___lam__0(
        v_ctx_6290_,
        v_lctx_6291_,
        v_stx_6292_,
        v_expectedType_x3f_6293_,
        v_info_6294_,
        v___y_6295_,
        v___y_6296_,
        v___y_6297_,
        v___y_6298_,
    );
    lean_dec(v___y_6298_);
    lean_dec_ref(v___y_6297_);
    lean_dec(v___y_6296_);
    lean_dec_ref(v___y_6295_);
    lean_dec_ref(v_info_6294_);
    return v_res_6300_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_format(
    mut v_ctx_6307_: *mut LeanObject,
    mut v_info_6308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_termInfo_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6314_: u8 = 0;
    let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6319_: u8 = 0;
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6331_: u8 = 0;
    let mut v_isSharedCheck_6332_: u8 = 0;
    let mut v_stx_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: u8 = 0;
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_info_6308_) {
                0 => {
                    v_termInfo_6310_ = lean_ctor_get(v_info_6308_, 0);
                    v_expectedType_x3f_6311_ = lean_ctor_get(v_info_6308_, 1);
                    v_isSharedCheck_6332_ = (!lean_is_exclusive(v_info_6308_)) as u8;
                    if v_isSharedCheck_6332_ == 0 {
                        v___x_6313_ = v_info_6308_;
                        v_isShared_6314_ = v_isSharedCheck_6332_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_expectedType_x3f_6311_);
                        lean_inc(v_termInfo_6310_);
                        lean_dec(v_info_6308_);
                        v___x_6313_ = lean_box(0);
                        v_isShared_6314_ = v_isSharedCheck_6332_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_stx_6333_ = lean_ctor_get(v_info_6308_, 0);
                    lean_inc(v_stx_6333_);
                    v_lctx_6334_ = lean_ctor_get(v_info_6308_, 2);
                    lean_inc_ref_n(v_lctx_6334_, 2);
                    v_expectedType_x3f_6335_ = lean_ctor_get(v_info_6308_, 3);
                    lean_inc(v_expectedType_x3f_6335_);
                    lean_inc_ref(v_ctx_6307_);
                    v___f_6336_ = lean_alloc_closure(
                        l_Lean_Elab_CompletionInfo_format___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    lean_closure_set(v___f_6336_, 0, v_ctx_6307_);
                    lean_closure_set(v___f_6336_, 1, v_lctx_6334_);
                    lean_closure_set(v___f_6336_, 2, v_stx_6333_);
                    lean_closure_set(v___f_6336_, 3, v_expectedType_x3f_6335_);
                    lean_closure_set(v___f_6336_, 4, v_info_6308_);
                    v___x_6337_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                        v_ctx_6307_,
                        v_lctx_6334_,
                        v___f_6336_,
                    );
                    return v___x_6337_;
                }
                _ => {
                    v___x_6338_ = l_Lean_Elab_CompletionInfo_format___closed__3;
                    v___x_6339_ = l_Lean_Elab_CompletionInfo_stx(v_info_6308_);
                    lean_dec_ref(v_info_6308_);
                    v___x_6340_ = lean_box(0);
                    v___x_6341_ = 0;
                    lean_inc(v___x_6339_);
                    v___x_6342_ = l_Lean_Syntax_formatStx(v___x_6339_, v___x_6340_, v___x_6341_);
                    v___x_6343_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6343_, 0, v___x_6338_);
                    lean_ctor_set(v___x_6343_, 1, v___x_6342_);
                    v___x_6344_ =
                        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
                    v___x_6345_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6345_, 0, v___x_6343_);
                    lean_ctor_set(v___x_6345_, 1, v___x_6344_);
                    v___x_6346_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(
                        v_ctx_6307_,
                        v___x_6339_,
                    );
                    lean_dec(v___x_6339_);
                    v___x_6347_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6347_, 0, v___x_6345_);
                    lean_ctor_set(v___x_6347_, 1, v___x_6346_);
                    v___x_6348_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6348_, 0, v___x_6347_);
                    return v___x_6348_;
                }
            },
            1 => {
                v___x_6315_ = l_Lean_Elab_TermInfo_format(v_ctx_6307_, v_termInfo_6310_);
                if lean_obj_tag(v___x_6315_) == 0 {
                    v_a_6316_ = lean_ctor_get(v___x_6315_, 0);
                    v_isSharedCheck_6331_ = (!lean_is_exclusive(v___x_6315_)) as u8;
                    if v_isSharedCheck_6331_ == 0 {
                        v___x_6318_ = v___x_6315_;
                        v_isShared_6319_ = v_isSharedCheck_6331_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6316_);
                        lean_dec(v___x_6315_);
                        v___x_6318_ = lean_box(0);
                        v_isShared_6319_ = v_isSharedCheck_6331_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6313_);
                    lean_dec(v_expectedType_x3f_6311_);
                    return v___x_6315_;
                }
            }
            2 => {
                v___x_6320_ = l_Lean_Elab_CompletionInfo_format___closed__1;
                if v_isShared_6314_ == 0 {
                    lean_ctor_set_tag(v___x_6313_, 5);
                    lean_ctor_set(v___x_6313_, 1, v_a_6316_);
                    lean_ctor_set(v___x_6313_, 0, v___x_6320_);
                    v___x_6322_ = v___x_6313_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6330_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6330_, 0, v___x_6320_);
                    lean_ctor_set(v_reuseFailAlloc_6330_, 1, v_a_6316_);
                    v___x_6322_ = v_reuseFailAlloc_6330_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6323_ = l_Lean_Elab_CompletionInfo_format___lam__0___closed__3;
                v___x_6324_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6324_, 0, v___x_6322_);
                lean_ctor_set(v___x_6324_, 1, v___x_6323_);
                v___x_6325_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(
                    v_expectedType_x3f_6311_,
                );
                v___x_6326_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6326_, 0, v___x_6324_);
                lean_ctor_set(v___x_6326_, 1, v___x_6325_);
                if v_isShared_6319_ == 0 {
                    lean_ctor_set(v___x_6318_, 0, v___x_6326_);
                    v___x_6328_ = v___x_6318_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6329_, 0, v___x_6326_);
                    v___x_6328_ = v_reuseFailAlloc_6329_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_format___boxed(
    mut v_ctx_6349_: *mut LeanObject,
    mut v_info_6350_: *mut LeanObject,
    mut v_a_6351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6352_: *mut LeanObject = core::ptr::null_mut();
    v_res_6352_ = l_Lean_Elab_CompletionInfo_format(v_ctx_6349_, v_info_6350_);
    return v_res_6352_;
}
pub unsafe fn l_Lean_Elab_CommandInfo_format(
    mut v_ctx_6356_: *mut LeanObject,
    mut v_info_6357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    v___x_6359_ = l_Lean_Elab_CommandInfo_format___closed__1;
    v___x_6360_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_6356_, v_info_6357_);
    v___x_6361_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6361_, 0, v___x_6359_);
    lean_ctor_set(v___x_6361_, 1, v___x_6360_);
    v___x_6362_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6362_, 0, v___x_6361_);
    return v___x_6362_;
}
pub unsafe fn l_Lean_Elab_CommandInfo_format___boxed(
    mut v_ctx_6363_: *mut LeanObject,
    mut v_info_6364_: *mut LeanObject,
    mut v_a_6365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6366_: *mut LeanObject = core::ptr::null_mut();
    v_res_6366_ = l_Lean_Elab_CommandInfo_format(v_ctx_6363_, v_info_6364_);
    return v_res_6366_;
}
pub unsafe fn l_Lean_Elab_OptionInfo_format(
    mut v_ctx_6370_: *mut LeanObject,
    mut v_info_6371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stx_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optionName_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: u8 = 0;
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    v_stx_6373_ = lean_ctor_get(v_info_6371_, 0);
    lean_inc(v_stx_6373_);
    v_optionName_6374_ = lean_ctor_get(v_info_6371_, 1);
    lean_inc(v_optionName_6374_);
    lean_dec_ref(v_info_6371_);
    v___x_6375_ = l_Lean_Elab_OptionInfo_format___closed__1;
    v___x_6376_ = 1;
    v___x_6377_ = l_Lean_Name_toString(v_optionName_6374_, v___x_6376_);
    v___x_6378_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6378_, 0, v___x_6377_);
    v___x_6379_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6379_, 0, v___x_6375_);
    lean_ctor_set(v___x_6379_, 1, v___x_6378_);
    v___x_6380_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
    v___x_6381_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6381_, 0, v___x_6379_);
    lean_ctor_set(v___x_6381_, 1, v___x_6380_);
    v___x_6382_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_6370_, v_stx_6373_);
    lean_dec(v_stx_6373_);
    v___x_6383_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6383_, 0, v___x_6381_);
    lean_ctor_set(v___x_6383_, 1, v___x_6382_);
    v___x_6384_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6384_, 0, v___x_6383_);
    return v___x_6384_;
}
pub unsafe fn l_Lean_Elab_OptionInfo_format___boxed(
    mut v_ctx_6385_: *mut LeanObject,
    mut v_info_6386_: *mut LeanObject,
    mut v_a_6387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6388_: *mut LeanObject = core::ptr::null_mut();
    v_res_6388_ = l_Lean_Elab_OptionInfo_format(v_ctx_6385_, v_info_6386_);
    return v_res_6388_;
}
pub unsafe fn l_Lean_Elab_ErrorNameInfo_format(
    mut v_ctx_6392_: *mut LeanObject,
    mut v_info_6393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stx_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorName_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6399_: u8 = 0;
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: u8 = 0;
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_6395_ = lean_ctor_get(v_info_6393_, 0);
                v_errorName_6396_ = lean_ctor_get(v_info_6393_, 1);
                v_isSharedCheck_6412_ = (!lean_is_exclusive(v_info_6393_)) as u8;
                if v_isSharedCheck_6412_ == 0 {
                    v___x_6398_ = v_info_6393_;
                    v_isShared_6399_ = v_isSharedCheck_6412_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_errorName_6396_);
                    lean_inc(v_stx_6395_);
                    lean_dec(v_info_6393_);
                    v___x_6398_ = lean_box(0);
                    v_isShared_6399_ = v_isSharedCheck_6412_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6400_ = l_Lean_Elab_ErrorNameInfo_format___closed__1;
                v___x_6401_ = 1;
                v___x_6402_ = l_Lean_Name_toString(v_errorName_6396_, v___x_6401_);
                v___x_6403_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6403_, 0, v___x_6402_);
                if v_isShared_6399_ == 0 {
                    lean_ctor_set_tag(v___x_6398_, 5);
                    lean_ctor_set(v___x_6398_, 1, v___x_6403_);
                    lean_ctor_set(v___x_6398_, 0, v___x_6400_);
                    v___x_6405_ = v___x_6398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6411_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6411_, 0, v___x_6400_);
                    lean_ctor_set(v_reuseFailAlloc_6411_, 1, v___x_6403_);
                    v___x_6405_ = v_reuseFailAlloc_6411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6406_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
                v___x_6407_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6407_, 0, v___x_6405_);
                lean_ctor_set(v___x_6407_, 1, v___x_6406_);
                v___x_6408_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(
                    v_ctx_6392_,
                    v_stx_6395_,
                );
                lean_dec(v_stx_6395_);
                v___x_6409_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6409_, 0, v___x_6407_);
                lean_ctor_set(v___x_6409_, 1, v___x_6408_);
                v___x_6410_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6410_, 0, v___x_6409_);
                return v___x_6410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ErrorNameInfo_format___boxed(
    mut v_ctx_6413_: *mut LeanObject,
    mut v_info_6414_: *mut LeanObject,
    mut v_a_6415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6416_: *mut LeanObject = core::ptr::null_mut();
    v_res_6416_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_6413_, v_info_6414_);
    return v_res_6416_;
}
pub unsafe fn l_Lean_Elab_FieldInfo_format___lam__0(
    mut v_val_6423_: *mut LeanObject,
    mut v_fieldName_6424_: *mut LeanObject,
    mut v_ctx_6425_: *mut LeanObject,
    mut v_stx_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
    mut v___y_6430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6438_: u8 = 0;
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6443_: u8 = 0;
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: u8 = 0;
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6464_: u8 = 0;
    let mut v_isSharedCheck_6465_: u8 = 0;
    let mut v_a_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6469_: u8 = 0;
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6430_);
                lean_inc_ref(v___y_6429_);
                lean_inc(v___y_6428_);
                lean_inc_ref(v___y_6427_);
                lean_inc_ref(v_val_6423_);
                v___x_6432_ = lean_infer_type(
                    v_val_6423_,
                    v___y_6427_,
                    v___y_6428_,
                    v___y_6429_,
                    v___y_6430_,
                );
                if lean_obj_tag(v___x_6432_) == 0 {
                    v_a_6433_ = lean_ctor_get(v___x_6432_, 0);
                    lean_inc(v_a_6433_);
                    lean_dec_ref_known(v___x_6432_, 1);
                    v___x_6434_ = l_Lean_Meta_ppExpr(
                        v_a_6433_,
                        v___y_6427_,
                        v___y_6428_,
                        v___y_6429_,
                        v___y_6430_,
                    );
                    if lean_obj_tag(v___x_6434_) == 0 {
                        v_a_6435_ = lean_ctor_get(v___x_6434_, 0);
                        v_isSharedCheck_6465_ = (!lean_is_exclusive(v___x_6434_)) as u8;
                        if v_isSharedCheck_6465_ == 0 {
                            v___x_6437_ = v___x_6434_;
                            v_isShared_6438_ = v_isSharedCheck_6465_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6435_);
                            lean_dec(v___x_6434_);
                            v___x_6437_ = lean_box(0);
                            v_isShared_6438_ = v_isSharedCheck_6465_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___y_6430_);
                        lean_dec_ref(v___y_6429_);
                        lean_dec(v___y_6428_);
                        lean_dec_ref(v___y_6427_);
                        lean_dec_ref(v_ctx_6425_);
                        lean_dec(v_fieldName_6424_);
                        lean_dec_ref(v_val_6423_);
                        return v___x_6434_;
                    }
                } else {
                    lean_dec(v___y_6430_);
                    lean_dec_ref(v___y_6429_);
                    lean_dec(v___y_6428_);
                    lean_dec_ref(v___y_6427_);
                    lean_dec_ref(v_ctx_6425_);
                    lean_dec(v_fieldName_6424_);
                    lean_dec_ref(v_val_6423_);
                    v_a_6466_ = lean_ctor_get(v___x_6432_, 0);
                    v_isSharedCheck_6473_ = (!lean_is_exclusive(v___x_6432_)) as u8;
                    if v_isSharedCheck_6473_ == 0 {
                        v___x_6468_ = v___x_6432_;
                        v_isShared_6469_ = v_isSharedCheck_6473_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6466_);
                        lean_dec(v___x_6432_);
                        v___x_6468_ = lean_box(0);
                        v_isShared_6469_ = v_isSharedCheck_6473_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6439_ = l_Lean_Meta_ppExpr(
                    v_val_6423_,
                    v___y_6427_,
                    v___y_6428_,
                    v___y_6429_,
                    v___y_6430_,
                );
                lean_dec(v___y_6430_);
                lean_dec_ref(v___y_6429_);
                lean_dec(v___y_6428_);
                lean_dec_ref(v___y_6427_);
                if lean_obj_tag(v___x_6439_) == 0 {
                    v_a_6440_ = lean_ctor_get(v___x_6439_, 0);
                    v_isSharedCheck_6464_ = (!lean_is_exclusive(v___x_6439_)) as u8;
                    if v_isSharedCheck_6464_ == 0 {
                        v___x_6442_ = v___x_6439_;
                        v_isShared_6443_ = v_isSharedCheck_6464_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6440_);
                        lean_dec(v___x_6439_);
                        v___x_6442_ = lean_box(0);
                        v_isShared_6443_ = v_isSharedCheck_6464_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6437_);
                    lean_dec(v_a_6435_);
                    lean_dec_ref(v_ctx_6425_);
                    lean_dec(v_fieldName_6424_);
                    return v___x_6439_;
                }
            }
            2 => {
                v___x_6444_ = l_Lean_Elab_FieldInfo_format___lam__0___closed__1;
                v___x_6445_ = 1;
                v___x_6446_ = l_Lean_Name_toString(v_fieldName_6424_, v___x_6445_);
                if v_isShared_6438_ == 0 {
                    lean_ctor_set_tag(v___x_6437_, 3);
                    lean_ctor_set(v___x_6437_, 0, v___x_6446_);
                    v___x_6448_ = v___x_6437_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6463_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6463_, 0, v___x_6446_);
                    v___x_6448_ = v_reuseFailAlloc_6463_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6449_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6449_, 0, v___x_6444_);
                lean_ctor_set(v___x_6449_, 1, v___x_6448_);
                v___x_6450_ = l_Lean_Elab_CompletionInfo_format___lam__0___closed__3;
                v___x_6451_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6451_, 0, v___x_6449_);
                lean_ctor_set(v___x_6451_, 1, v___x_6450_);
                v___x_6452_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6452_, 0, v___x_6451_);
                lean_ctor_set(v___x_6452_, 1, v_a_6435_);
                v___x_6453_ = l_Lean_Elab_FieldInfo_format___lam__0___closed__3;
                v___x_6454_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6454_, 0, v___x_6452_);
                lean_ctor_set(v___x_6454_, 1, v___x_6453_);
                v___x_6455_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6455_, 0, v___x_6454_);
                lean_ctor_set(v___x_6455_, 1, v_a_6440_);
                v___x_6456_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
                v___x_6457_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6457_, 0, v___x_6455_);
                lean_ctor_set(v___x_6457_, 1, v___x_6456_);
                v___x_6458_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(
                    v_ctx_6425_,
                    v_stx_6426_,
                );
                v___x_6459_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6459_, 0, v___x_6457_);
                lean_ctor_set(v___x_6459_, 1, v___x_6458_);
                if v_isShared_6443_ == 0 {
                    lean_ctor_set(v___x_6442_, 0, v___x_6459_);
                    v___x_6461_ = v___x_6442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6462_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6459_);
                    v___x_6461_ = v_reuseFailAlloc_6462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6461_;
            }
            5 => {
                if v_isShared_6469_ == 0 {
                    v___x_6471_ = v___x_6468_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_a_6466_);
                    v___x_6471_ = v_reuseFailAlloc_6472_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_FieldInfo_format___lam__0___boxed(
    mut v_val_6474_: *mut LeanObject,
    mut v_fieldName_6475_: *mut LeanObject,
    mut v_ctx_6476_: *mut LeanObject,
    mut v_stx_6477_: *mut LeanObject,
    mut v___y_6478_: *mut LeanObject,
    mut v___y_6479_: *mut LeanObject,
    mut v___y_6480_: *mut LeanObject,
    mut v___y_6481_: *mut LeanObject,
    mut v___y_6482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6483_: *mut LeanObject = core::ptr::null_mut();
    v_res_6483_ = l_Lean_Elab_FieldInfo_format___lam__0(
        v_val_6474_,
        v_fieldName_6475_,
        v_ctx_6476_,
        v_stx_6477_,
        v___y_6478_,
        v___y_6479_,
        v___y_6480_,
        v___y_6481_,
    );
    lean_dec(v_stx_6477_);
    return v_res_6483_;
}
pub unsafe fn l_Lean_Elab_FieldInfo_format(
    mut v_ctx_6484_: *mut LeanObject,
    mut v_info_6485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fieldName_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    v_fieldName_6487_ = lean_ctor_get(v_info_6485_, 1);
    lean_inc(v_fieldName_6487_);
    v_lctx_6488_ = lean_ctor_get(v_info_6485_, 2);
    lean_inc_ref(v_lctx_6488_);
    v_val_6489_ = lean_ctor_get(v_info_6485_, 3);
    lean_inc_ref(v_val_6489_);
    v_stx_6490_ = lean_ctor_get(v_info_6485_, 4);
    lean_inc(v_stx_6490_);
    lean_dec_ref(v_info_6485_);
    lean_inc_ref(v_ctx_6484_);
    v___f_6491_ = lean_alloc_closure(
        l_Lean_Elab_FieldInfo_format___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_6491_, 0, v_val_6489_);
    lean_closure_set(v___f_6491_, 1, v_fieldName_6487_);
    lean_closure_set(v___f_6491_, 2, v_ctx_6484_);
    lean_closure_set(v___f_6491_, 3, v_stx_6490_);
    v___x_6492_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6484_, v_lctx_6488_, v___f_6491_);
    return v___x_6492_;
}
pub unsafe fn l_Lean_Elab_FieldInfo_format___boxed(
    mut v_ctx_6493_: *mut LeanObject,
    mut v_info_6494_: *mut LeanObject,
    mut v_a_6495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6496_: *mut LeanObject = core::ptr::null_mut();
    v_res_6496_ = l_Lean_Elab_FieldInfo_format(v_ctx_6493_, v_info_6494_);
    return v_res_6496_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(
    mut v_pre_6497_: *mut LeanObject,
    mut v_x_6498_: *mut LeanObject,
    mut v_x_6499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6504_: u8 = 0;
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6499_) == 0 {
                    lean_dec(v_pre_6497_);
                    return v_x_6498_;
                } else {
                    v_head_6500_ = lean_ctor_get(v_x_6499_, 0);
                    v_tail_6501_ = lean_ctor_get(v_x_6499_, 1);
                    v_isSharedCheck_6510_ = (!lean_is_exclusive(v_x_6499_)) as u8;
                    if v_isSharedCheck_6510_ == 0 {
                        v___x_6503_ = v_x_6499_;
                        v_isShared_6504_ = v_isSharedCheck_6510_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6501_);
                        lean_inc(v_head_6500_);
                        lean_dec(v_x_6499_);
                        v___x_6503_ = lean_box(0);
                        v_isShared_6504_ = v_isSharedCheck_6510_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_pre_6497_);
                if v_isShared_6504_ == 0 {
                    lean_ctor_set_tag(v___x_6503_, 5);
                    lean_ctor_set(v___x_6503_, 1, v_pre_6497_);
                    lean_ctor_set(v___x_6503_, 0, v_x_6498_);
                    v___x_6506_ = v___x_6503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6509_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6509_, 0, v_x_6498_);
                    lean_ctor_set(v_reuseFailAlloc_6509_, 1, v_pre_6497_);
                    v___x_6506_ = v_reuseFailAlloc_6509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6507_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6507_, 0, v___x_6506_);
                lean_ctor_set(v___x_6507_, 1, v_head_6500_);
                v_x_6498_ = v___x_6507_;
                v_x_6499_ = v_tail_6501_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(
    mut v_pre_6511_: *mut LeanObject,
    mut v_x_6512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6518_: u8 = 0;
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6512_) == 0 {
                    lean_dec(v_pre_6511_);
                    v___x_6513_ = lean_box(0);
                    return v___x_6513_;
                } else {
                    v_head_6514_ = lean_ctor_get(v_x_6512_, 0);
                    v_tail_6515_ = lean_ctor_get(v_x_6512_, 1);
                    v_isSharedCheck_6523_ = (!lean_is_exclusive(v_x_6512_)) as u8;
                    if v_isSharedCheck_6523_ == 0 {
                        v___x_6517_ = v_x_6512_;
                        v_isShared_6518_ = v_isSharedCheck_6523_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6515_);
                        lean_inc(v_head_6514_);
                        lean_dec(v_x_6512_);
                        v___x_6517_ = lean_box(0);
                        v_isShared_6518_ = v_isSharedCheck_6523_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_pre_6511_);
                if v_isShared_6518_ == 0 {
                    lean_ctor_set_tag(v___x_6517_, 5);
                    lean_ctor_set(v___x_6517_, 1, v_head_6514_);
                    lean_ctor_set(v___x_6517_, 0, v_pre_6511_);
                    v___x_6520_ = v___x_6517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6522_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6522_, 0, v_pre_6511_);
                    lean_ctor_set(v_reuseFailAlloc_6522_, 1, v_head_6514_);
                    v___x_6520_ = v_reuseFailAlloc_6522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6521_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_6511_, v___x_6520_, v_tail_6515_);
                return v___x_6521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(
    mut v_x_6524_: *mut LeanObject,
    mut v_x_6525_: *mut LeanObject,
    mut v___y_6526_: *mut LeanObject,
    mut v___y_6527_: *mut LeanObject,
    mut v___y_6528_: *mut LeanObject,
    mut v___y_6529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6547_: u8 = 0;
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6551_: u8 = 0;
    let mut v_isSharedCheck_6552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6524_) == 0 {
                    v___x_6531_ = l_List_reverse___redArg(v_x_6525_);
                    v___x_6532_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6532_, 0, v___x_6531_);
                    return v___x_6532_;
                } else {
                    v_head_6533_ = lean_ctor_get(v_x_6524_, 0);
                    v_tail_6534_ = lean_ctor_get(v_x_6524_, 1);
                    v_isSharedCheck_6552_ = (!lean_is_exclusive(v_x_6524_)) as u8;
                    if v_isSharedCheck_6552_ == 0 {
                        v___x_6536_ = v_x_6524_;
                        v_isShared_6537_ = v_isSharedCheck_6552_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6534_);
                        lean_inc(v_head_6533_);
                        lean_dec(v_x_6524_);
                        v___x_6536_ = lean_box(0);
                        v_isShared_6537_ = v_isSharedCheck_6552_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6538_ = l_Lean_Meta_ppGoal(
                    v_head_6533_,
                    v___y_6526_,
                    v___y_6527_,
                    v___y_6528_,
                    v___y_6529_,
                );
                lean_dec(v_head_6533_);
                if lean_obj_tag(v___x_6538_) == 0 {
                    v_a_6539_ = lean_ctor_get(v___x_6538_, 0);
                    lean_inc(v_a_6539_);
                    lean_dec_ref_known(v___x_6538_, 1);
                    if v_isShared_6537_ == 0 {
                        lean_ctor_set(v___x_6536_, 1, v_x_6525_);
                        lean_ctor_set(v___x_6536_, 0, v_a_6539_);
                        v___x_6541_ = v___x_6536_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6543_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6539_);
                        lean_ctor_set(v_reuseFailAlloc_6543_, 1, v_x_6525_);
                        v___x_6541_ = v_reuseFailAlloc_6543_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6536_);
                    lean_dec(v_tail_6534_);
                    lean_dec(v_x_6525_);
                    v_a_6544_ = lean_ctor_get(v___x_6538_, 0);
                    v_isSharedCheck_6551_ = (!lean_is_exclusive(v___x_6538_)) as u8;
                    if v_isSharedCheck_6551_ == 0 {
                        v___x_6546_ = v___x_6538_;
                        v_isShared_6547_ = v_isSharedCheck_6551_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6544_);
                        lean_dec(v___x_6538_);
                        v___x_6546_ = lean_box(0);
                        v_isShared_6547_ = v_isSharedCheck_6551_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_6524_ = v_tail_6534_;
                v_x_6525_ = v___x_6541_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6547_ == 0 {
                    v___x_6549_ = v___x_6546_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_a_6544_);
                    v___x_6549_ = v_reuseFailAlloc_6550_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(
    mut v_x_6553_: *mut LeanObject,
    mut v_x_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
    mut v___y_6557_: *mut LeanObject,
    mut v___y_6558_: *mut LeanObject,
    mut v___y_6559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6560_: *mut LeanObject = core::ptr::null_mut();
    v_res_6560_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(
        v_x_6553_,
        v_x_6554_,
        v___y_6555_,
        v___y_6556_,
        v___y_6557_,
        v___y_6558_,
    );
    lean_dec(v___y_6558_);
    lean_dec_ref(v___y_6557_);
    lean_dec(v___y_6556_);
    lean_dec_ref(v___y_6555_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_ppGoals___lam__0(
    mut v_goals_6564_: *mut LeanObject,
    mut v___x_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
    mut v___y_6569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6575_: u8 = 0;
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6581_: u8 = 0;
    let mut v_a_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6585_: u8 = 0;
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6571_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(
                    v_goals_6564_,
                    v___x_6565_,
                    v___y_6566_,
                    v___y_6567_,
                    v___y_6568_,
                    v___y_6569_,
                );
                if lean_obj_tag(v___x_6571_) == 0 {
                    v_a_6572_ = lean_ctor_get(v___x_6571_, 0);
                    v_isSharedCheck_6581_ = (!lean_is_exclusive(v___x_6571_)) as u8;
                    if v_isSharedCheck_6581_ == 0 {
                        v___x_6574_ = v___x_6571_;
                        v_isShared_6575_ = v_isSharedCheck_6581_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6572_);
                        lean_dec(v___x_6571_);
                        v___x_6574_ = lean_box(0);
                        v_isShared_6575_ = v_isSharedCheck_6581_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6582_ = lean_ctor_get(v___x_6571_, 0);
                    v_isSharedCheck_6589_ = (!lean_is_exclusive(v___x_6571_)) as u8;
                    if v_isSharedCheck_6589_ == 0 {
                        v___x_6584_ = v___x_6571_;
                        v_isShared_6585_ = v_isSharedCheck_6589_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6582_);
                        lean_dec(v___x_6571_);
                        v___x_6584_ = lean_box(0);
                        v_isShared_6585_ = v_isSharedCheck_6589_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6576_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1;
                v___x_6577_ =
                    l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(
                        v___x_6576_,
                        v_a_6572_,
                    );
                if v_isShared_6575_ == 0 {
                    lean_ctor_set(v___x_6574_, 0, v___x_6577_);
                    v___x_6579_ = v___x_6574_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6580_, 0, v___x_6577_);
                    v___x_6579_ = v_reuseFailAlloc_6580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6579_;
            }
            3 => {
                if v_isShared_6585_ == 0 {
                    v___x_6587_ = v___x_6584_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6588_, 0, v_a_6582_);
                    v___x_6587_ = v_reuseFailAlloc_6588_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(
    mut v_goals_6590_: *mut LeanObject,
    mut v___x_6591_: *mut LeanObject,
    mut v___y_6592_: *mut LeanObject,
    mut v___y_6593_: *mut LeanObject,
    mut v___y_6594_: *mut LeanObject,
    mut v___y_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6597_: *mut LeanObject = core::ptr::null_mut();
    v_res_6597_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(
        v_goals_6590_,
        v___x_6591_,
        v___y_6592_,
        v___y_6593_,
        v___y_6594_,
        v___y_6595_,
    );
    lean_dec(v___y_6595_);
    lean_dec_ref(v___y_6594_);
    lean_dec(v___y_6593_);
    lean_dec_ref(v___y_6592_);
    return v_res_6597_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0() -> *mut LeanObject {
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    v___x_6598_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6598_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1() -> *mut LeanObject {
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    v___x_6599_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__0_once),
        _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0,
    );
    v___x_6600_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6600_, 0, v___x_6599_);
    return v___x_6600_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2() -> *mut LeanObject {
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    v___x_6601_ = lean_unsigned_to_nat(32);
    v___x_6602_ = lean_mk_empty_array_with_capacity(v___x_6601_);
    v___x_6603_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6603_, 0, v___x_6602_);
    return v___x_6603_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3() -> *mut LeanObject {
    let mut v___x_6604_: usize = 0;
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    v___x_6604_ = 5usize;
    v___x_6605_ = lean_unsigned_to_nat(0);
    v___x_6606_ = lean_unsigned_to_nat(32);
    v___x_6607_ = lean_mk_empty_array_with_capacity(v___x_6606_);
    v___x_6608_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__2_once),
        _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2,
    );
    v___x_6609_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6609_, 0, v___x_6608_);
    lean_ctor_set(v___x_6609_, 1, v___x_6607_);
    lean_ctor_set(v___x_6609_, 2, v___x_6605_);
    lean_ctor_set(v___x_6609_, 3, v___x_6605_);
    lean_ctor_set_usize(v___x_6609_, 4, v___x_6604_);
    return v___x_6609_;
}
pub unsafe fn _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4() -> *mut LeanObject {
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    v___x_6610_ = lean_box(1);
    v___x_6611_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__3_once),
        _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3,
    );
    v___x_6612_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__1_once),
        _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1,
    );
    v___x_6613_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6613_, 0, v___x_6612_);
    lean_ctor_set(v___x_6613_, 1, v___x_6611_);
    lean_ctor_set(v___x_6613_, 2, v___x_6610_);
    return v___x_6613_;
}
pub unsafe fn l_Lean_Elab_ContextInfo_ppGoals(
    mut v_ctx_6617_: *mut LeanObject,
    mut v_goals_6618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6620_: u8 = 0;
    v___x_6620_ = l_List_isEmpty___redArg(v_goals_6618_);
    if v___x_6620_ == 0 {
        let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
        v___x_6621_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__4_once),
            _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4,
        );
        v___x_6622_ = lean_box(0);
        v___f_6623_ = lean_alloc_closure(
            l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___f_6623_, 0, v_goals_6618_);
        lean_closure_set(v___f_6623_, 1, v___x_6622_);
        v___x_6624_ =
            l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_6617_, v___x_6621_, v___f_6623_);
        return v___x_6624_;
    } else {
        let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_goals_6618_);
        lean_dec_ref(v_ctx_6617_);
        v___x_6625_ = l_Lean_Elab_ContextInfo_ppGoals___closed__6;
        v___x_6626_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6626_, 0, v___x_6625_);
        return v___x_6626_;
    }
}
pub unsafe fn l_Lean_Elab_ContextInfo_ppGoals___boxed(
    mut v_ctx_6627_: *mut LeanObject,
    mut v_goals_6628_: *mut LeanObject,
    mut v_a_6629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6630_: *mut LeanObject = core::ptr::null_mut();
    v_res_6630_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_6627_, v_goals_6628_);
    return v_res_6630_;
}
pub unsafe fn l_Lean_Elab_TacticInfo_format(
    mut v_ctx_6640_: *mut LeanObject,
    mut v_info_6641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toCommandContextInfo_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_x3f_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_autoImplicits_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdEnv_x3f_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6655_: u8 = 0;
    let mut v_toElabInfo_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctxBefore_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctxAfter_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsAfter_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctxB_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctxA_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6672_: u8 = 0;
    let mut v_stx_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: u8 = 0;
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6692_: u8 = 0;
    let mut v_reuseFailAlloc_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6694_: u8 = 0;
    let mut v_unused_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toCommandContextInfo_6643_ = lean_ctor_get(v_ctx_6640_, 0);
                lean_inc_ref(v_toCommandContextInfo_6643_);
                v_parentDecl_x3f_6644_ = lean_ctor_get(v_ctx_6640_, 1);
                v_autoImplicits_6645_ = lean_ctor_get(v_ctx_6640_, 2);
                v_env_6646_ = lean_ctor_get(v_toCommandContextInfo_6643_, 0);
                v_cmdEnv_x3f_6647_ = lean_ctor_get(v_toCommandContextInfo_6643_, 1);
                v_fileMap_6648_ = lean_ctor_get(v_toCommandContextInfo_6643_, 2);
                v_options_6649_ = lean_ctor_get(v_toCommandContextInfo_6643_, 4);
                v_currNamespace_6650_ = lean_ctor_get(v_toCommandContextInfo_6643_, 5);
                v_openDecls_6651_ = lean_ctor_get(v_toCommandContextInfo_6643_, 6);
                v_ngen_6652_ = lean_ctor_get(v_toCommandContextInfo_6643_, 7);
                v_isSharedCheck_6694_ = (!lean_is_exclusive(v_toCommandContextInfo_6643_)) as u8;
                if v_isSharedCheck_6694_ == 0 {
                    v_unused_6695_ = lean_ctor_get(v_toCommandContextInfo_6643_, 3);
                    lean_dec(v_unused_6695_);
                    v___x_6654_ = v_toCommandContextInfo_6643_;
                    v_isShared_6655_ = v_isSharedCheck_6694_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ngen_6652_);
                    lean_inc(v_openDecls_6651_);
                    lean_inc(v_currNamespace_6650_);
                    lean_inc(v_options_6649_);
                    lean_inc(v_fileMap_6648_);
                    lean_inc(v_cmdEnv_x3f_6647_);
                    lean_inc(v_env_6646_);
                    lean_dec(v_toCommandContextInfo_6643_);
                    v___x_6654_ = lean_box(0);
                    v_isShared_6655_ = v_isSharedCheck_6694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toElabInfo_6656_ = lean_ctor_get(v_info_6641_, 0);
                lean_inc_ref(v_toElabInfo_6656_);
                v_mctxBefore_6657_ = lean_ctor_get(v_info_6641_, 1);
                lean_inc_ref(v_mctxBefore_6657_);
                v_goalsBefore_6658_ = lean_ctor_get(v_info_6641_, 2);
                lean_inc(v_goalsBefore_6658_);
                v_mctxAfter_6659_ = lean_ctor_get(v_info_6641_, 3);
                lean_inc_ref(v_mctxAfter_6659_);
                v_goalsAfter_6660_ = lean_ctor_get(v_info_6641_, 4);
                lean_inc(v_goalsAfter_6660_);
                lean_dec_ref(v_info_6641_);
                lean_inc_ref(v_ngen_6652_);
                lean_inc(v_openDecls_6651_);
                lean_inc(v_currNamespace_6650_);
                lean_inc_ref(v_options_6649_);
                lean_inc_ref(v_fileMap_6648_);
                lean_inc(v_cmdEnv_x3f_6647_);
                lean_inc_ref(v_env_6646_);
                if v_isShared_6655_ == 0 {
                    lean_ctor_set(v___x_6654_, 3, v_mctxBefore_6657_);
                    v___x_6662_ = v___x_6654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6693_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 0, v_env_6646_);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 1, v_cmdEnv_x3f_6647_);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 2, v_fileMap_6648_);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 3, v_mctxBefore_6657_);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 4, v_options_6649_);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 5, v_currNamespace_6650_);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 6, v_openDecls_6651_);
                    lean_ctor_set(v_reuseFailAlloc_6693_, 7, v_ngen_6652_);
                    v___x_6662_ = v_reuseFailAlloc_6693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_autoImplicits_6645_);
                lean_inc(v_parentDecl_x3f_6644_);
                v_ctxB_6663_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v_ctxB_6663_, 0, v___x_6662_);
                lean_ctor_set(v_ctxB_6663_, 1, v_parentDecl_x3f_6644_);
                lean_ctor_set(v_ctxB_6663_, 2, v_autoImplicits_6645_);
                v___x_6664_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_6663_, v_goalsBefore_6658_);
                if lean_obj_tag(v___x_6664_) == 0 {
                    v_a_6665_ = lean_ctor_get(v___x_6664_, 0);
                    lean_inc(v_a_6665_);
                    lean_dec_ref_known(v___x_6664_, 1);
                    v___x_6666_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_6666_, 0, v_env_6646_);
                    lean_ctor_set(v___x_6666_, 1, v_cmdEnv_x3f_6647_);
                    lean_ctor_set(v___x_6666_, 2, v_fileMap_6648_);
                    lean_ctor_set(v___x_6666_, 3, v_mctxAfter_6659_);
                    lean_ctor_set(v___x_6666_, 4, v_options_6649_);
                    lean_ctor_set(v___x_6666_, 5, v_currNamespace_6650_);
                    lean_ctor_set(v___x_6666_, 6, v_openDecls_6651_);
                    lean_ctor_set(v___x_6666_, 7, v_ngen_6652_);
                    lean_inc_ref(v_autoImplicits_6645_);
                    lean_inc(v_parentDecl_x3f_6644_);
                    v_ctxA_6667_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_ctxA_6667_, 0, v___x_6666_);
                    lean_ctor_set(v_ctxA_6667_, 1, v_parentDecl_x3f_6644_);
                    lean_ctor_set(v_ctxA_6667_, 2, v_autoImplicits_6645_);
                    v___x_6668_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_6667_, v_goalsAfter_6660_);
                    if lean_obj_tag(v___x_6668_) == 0 {
                        v_a_6669_ = lean_ctor_get(v___x_6668_, 0);
                        v_isSharedCheck_6692_ = (!lean_is_exclusive(v___x_6668_)) as u8;
                        if v_isSharedCheck_6692_ == 0 {
                            v___x_6671_ = v___x_6668_;
                            v_isShared_6672_ = v_isSharedCheck_6692_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6669_);
                            lean_dec(v___x_6668_);
                            v___x_6671_ = lean_box(0);
                            v_isShared_6672_ = v_isSharedCheck_6692_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6665_);
                        lean_dec_ref(v_toElabInfo_6656_);
                        lean_dec_ref(v_ctx_6640_);
                        return v___x_6668_;
                    }
                } else {
                    lean_dec(v_goalsAfter_6660_);
                    lean_dec_ref(v_mctxAfter_6659_);
                    lean_dec_ref(v_toElabInfo_6656_);
                    lean_dec_ref(v_ngen_6652_);
                    lean_dec(v_openDecls_6651_);
                    lean_dec(v_currNamespace_6650_);
                    lean_dec_ref(v_options_6649_);
                    lean_dec_ref(v_fileMap_6648_);
                    lean_dec(v_cmdEnv_x3f_6647_);
                    lean_dec_ref(v_env_6646_);
                    lean_dec_ref(v_ctx_6640_);
                    return v___x_6664_;
                }
            }
            3 => {
                v_stx_6673_ = lean_ctor_get(v_toElabInfo_6656_, 1);
                lean_inc(v_stx_6673_);
                v___x_6674_ = l_Lean_Elab_TacticInfo_format___closed__1;
                v___x_6675_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(
                    v_ctx_6640_,
                    v_toElabInfo_6656_,
                );
                v___x_6676_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6676_, 0, v___x_6674_);
                lean_ctor_set(v___x_6676_, 1, v___x_6675_);
                v___x_6677_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1;
                v___x_6678_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6678_, 0, v___x_6676_);
                lean_ctor_set(v___x_6678_, 1, v___x_6677_);
                v___x_6679_ = lean_box(0);
                v___x_6680_ = 0;
                v___x_6681_ = l_Lean_Syntax_formatStx(v_stx_6673_, v___x_6679_, v___x_6680_);
                v___x_6682_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6682_, 0, v___x_6678_);
                lean_ctor_set(v___x_6682_, 1, v___x_6681_);
                v___x_6683_ = l_Lean_Elab_TacticInfo_format___closed__3;
                v___x_6684_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6684_, 0, v___x_6682_);
                lean_ctor_set(v___x_6684_, 1, v___x_6683_);
                v___x_6685_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6685_, 0, v___x_6684_);
                lean_ctor_set(v___x_6685_, 1, v_a_6665_);
                v___x_6686_ = l_Lean_Elab_TacticInfo_format___closed__5;
                v___x_6687_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6687_, 0, v___x_6685_);
                lean_ctor_set(v___x_6687_, 1, v___x_6686_);
                v___x_6688_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6688_, 0, v___x_6687_);
                lean_ctor_set(v___x_6688_, 1, v_a_6669_);
                if v_isShared_6672_ == 0 {
                    lean_ctor_set(v___x_6671_, 0, v___x_6688_);
                    v___x_6690_ = v___x_6671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6691_, 0, v___x_6688_);
                    v___x_6690_ = v_reuseFailAlloc_6691_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TacticInfo_format___boxed(
    mut v_ctx_6696_: *mut LeanObject,
    mut v_info_6697_: *mut LeanObject,
    mut v_a_6698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6699_: *mut LeanObject = core::ptr::null_mut();
    v_res_6699_ = l_Lean_Elab_TacticInfo_format(v_ctx_6696_, v_info_6697_);
    return v_res_6699_;
}
pub unsafe fn l_Lean_Elab_MacroExpansionInfo_format(
    mut v_ctx_6706_: *mut LeanObject,
    mut v_info_6707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_output_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_6709_ = lean_ctor_get(v_info_6707_, 0);
                lean_inc_ref_n(v_lctx_6709_, 2);
                v_stx_6710_ = lean_ctor_get(v_info_6707_, 1);
                lean_inc(v_stx_6710_);
                v_output_6711_ = lean_ctor_get(v_info_6707_, 2);
                lean_inc(v_output_6711_);
                lean_dec_ref(v_info_6707_);
                v___x_6712_ =
                    l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_6706_, v_lctx_6709_, v_stx_6710_);
                v_a_6713_ = lean_ctor_get(v___x_6712_, 0);
                lean_inc(v_a_6713_);
                lean_dec_ref(v___x_6712_);
                v___x_6714_ =
                    l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_6706_, v_lctx_6709_, v_output_6711_);
                v_a_6715_ = lean_ctor_get(v___x_6714_, 0);
                v_isSharedCheck_6727_ = (!lean_is_exclusive(v___x_6714_)) as u8;
                if v_isSharedCheck_6727_ == 0 {
                    v___x_6717_ = v___x_6714_;
                    v_isShared_6718_ = v_isSharedCheck_6727_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6715_);
                    lean_dec(v___x_6714_);
                    v___x_6717_ = lean_box(0);
                    v_isShared_6718_ = v_isSharedCheck_6727_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6719_ = l_Lean_Elab_MacroExpansionInfo_format___closed__1;
                v___x_6720_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6720_, 0, v___x_6719_);
                lean_ctor_set(v___x_6720_, 1, v_a_6713_);
                v___x_6721_ = l_Lean_Elab_MacroExpansionInfo_format___closed__3;
                v___x_6722_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6722_, 0, v___x_6720_);
                lean_ctor_set(v___x_6722_, 1, v___x_6721_);
                v___x_6723_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6723_, 0, v___x_6722_);
                lean_ctor_set(v___x_6723_, 1, v_a_6715_);
                if v_isShared_6718_ == 0 {
                    lean_ctor_set(v___x_6717_, 0, v___x_6723_);
                    v___x_6725_ = v___x_6717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6726_, 0, v___x_6723_);
                    v___x_6725_ = v_reuseFailAlloc_6726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_MacroExpansionInfo_format___boxed(
    mut v_ctx_6728_: *mut LeanObject,
    mut v_info_6729_: *mut LeanObject,
    mut v_a_6730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6731_: *mut LeanObject = core::ptr::null_mut();
    v_res_6731_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_6728_, v_info_6729_);
    lean_dec_ref(v_ctx_6728_);
    return v_res_6731_;
}
pub unsafe fn _init_l_Lean_Elab_UserWidgetInfo_format___closed__0() -> *mut LeanObject {
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    v___x_6732_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6732_;
}
pub unsafe fn _init_l_Lean_Elab_UserWidgetInfo_format___closed__1() -> *mut LeanObject {
    let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    v___x_6733_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_UserWidgetInfo_format___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_UserWidgetInfo_format___closed__0_once),
        _init_l_Lean_Elab_UserWidgetInfo_format___closed__0,
    );
    v___x_6734_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6734_, 0, v___x_6733_);
    return v___x_6734_;
}
pub unsafe fn _init_l_Lean_Elab_UserWidgetInfo_format___closed__2() -> *mut LeanObject {
    let mut v___x_6735_: u8 = 0;
    let mut v___x_6736_: usize = 0;
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    v___x_6735_ = 1;
    v___x_6736_ = 0usize;
    v___x_6737_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_UserWidgetInfo_format___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_UserWidgetInfo_format___closed__1_once),
        _init_l_Lean_Elab_UserWidgetInfo_format___closed__1,
    );
    v___x_6738_ = lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1 + 1) as u32);
    lean_ctor_set(v___x_6738_, 0, v___x_6737_);
    lean_ctor_set(v___x_6738_, 1, v___x_6737_);
    lean_ctor_set_usize(v___x_6738_, 2, v___x_6736_);
    lean_ctor_set_uint8(
        v___x_6738_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_6735_,
    );
    return v___x_6738_;
}
pub unsafe fn l_Lean_Elab_UserWidgetInfo_format(
    mut v_info_6742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toWidgetInstance_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6746_: u8 = 0;
    let mut v_id_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_props_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6754_: u8 = 0;
    let mut v___x_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: u8 = 0;
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6770_: u8 = 0;
    let mut v_unused_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6772_: u8 = 0;
    let mut v_unused_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toWidgetInstance_6743_ = lean_ctor_get(v_info_6742_, 0);
                v_isSharedCheck_6772_ = (!lean_is_exclusive(v_info_6742_)) as u8;
                if v_isSharedCheck_6772_ == 0 {
                    v_unused_6773_ = lean_ctor_get(v_info_6742_, 1);
                    lean_dec(v_unused_6773_);
                    v___x_6745_ = v_info_6742_;
                    v_isShared_6746_ = v_isSharedCheck_6772_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toWidgetInstance_6743_);
                    lean_dec(v_info_6742_);
                    v___x_6745_ = lean_box(0);
                    v_isShared_6746_ = v_isSharedCheck_6772_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_6747_ = lean_ctor_get(v_toWidgetInstance_6743_, 0);
                lean_inc(v_id_6747_);
                v_props_6748_ = lean_ctor_get(v_toWidgetInstance_6743_, 1);
                lean_inc_ref(v_props_6748_);
                lean_dec_ref(v_toWidgetInstance_6743_);
                v___x_6749_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_UserWidgetInfo_format___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Elab_UserWidgetInfo_format___closed__2_once),
                    _init_l_Lean_Elab_UserWidgetInfo_format___closed__2,
                );
                v___x_6750_ = lean_apply_1(v_props_6748_, v___x_6749_);
                v_fst_6751_ = lean_ctor_get(v___x_6750_, 0);
                v_isSharedCheck_6770_ = (!lean_is_exclusive(v___x_6750_)) as u8;
                if v_isSharedCheck_6770_ == 0 {
                    v_unused_6771_ = lean_ctor_get(v___x_6750_, 1);
                    lean_dec(v_unused_6771_);
                    v___x_6753_ = v___x_6750_;
                    v_isShared_6754_ = v_isSharedCheck_6770_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_6751_);
                    lean_dec(v___x_6750_);
                    v___x_6753_ = lean_box(0);
                    v_isShared_6754_ = v_isSharedCheck_6770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6755_ = l_Lean_Elab_UserWidgetInfo_format___closed__4;
                v___x_6756_ = 1;
                v___x_6757_ = l_Lean_Name_toString(v_id_6747_, v___x_6756_);
                v___x_6758_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6758_, 0, v___x_6757_);
                if v_isShared_6754_ == 0 {
                    lean_ctor_set_tag(v___x_6753_, 5);
                    lean_ctor_set(v___x_6753_, 1, v___x_6758_);
                    lean_ctor_set(v___x_6753_, 0, v___x_6755_);
                    v___x_6760_ = v___x_6753_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6769_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6769_, 0, v___x_6755_);
                    lean_ctor_set(v_reuseFailAlloc_6769_, 1, v___x_6758_);
                    v___x_6760_ = v_reuseFailAlloc_6769_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6761_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1;
                if v_isShared_6746_ == 0 {
                    lean_ctor_set_tag(v___x_6745_, 5);
                    lean_ctor_set(v___x_6745_, 1, v___x_6761_);
                    lean_ctor_set(v___x_6745_, 0, v___x_6760_);
                    v___x_6763_ = v___x_6745_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6768_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6768_, 0, v___x_6760_);
                    lean_ctor_set(v_reuseFailAlloc_6768_, 1, v___x_6761_);
                    v___x_6763_ = v_reuseFailAlloc_6768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6764_ = lean_unsigned_to_nat(80);
                v___x_6765_ = l_Lean_Json_pretty(v_fst_6751_, v___x_6764_);
                v___x_6766_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6766_, 0, v___x_6765_);
                v___x_6767_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6767_, 0, v___x_6763_);
                lean_ctor_set(v___x_6767_, 1, v___x_6766_);
                return v___x_6767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_FVarAliasInfo_format(
    mut v_info_6780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userName_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseId_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: u8 = 0;
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut LeanObject = core::ptr::null_mut();
    v_userName_6781_ = lean_ctor_get(v_info_6780_, 0);
    lean_inc(v_userName_6781_);
    v_id_6782_ = lean_ctor_get(v_info_6780_, 1);
    lean_inc(v_id_6782_);
    v_baseId_6783_ = lean_ctor_get(v_info_6780_, 2);
    lean_inc(v_baseId_6783_);
    lean_dec_ref(v_info_6780_);
    v___x_6784_ = l_Lean_Elab_FVarAliasInfo_format___closed__1;
    v___x_6785_ = lean_erase_macro_scopes(v_userName_6781_);
    v___x_6786_ = 1;
    v___x_6787_ = l_Lean_Name_toString(v___x_6785_, v___x_6786_);
    v___x_6788_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6788_, 0, v___x_6787_);
    v___x_6789_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6789_, 0, v___x_6784_);
    lean_ctor_set(v___x_6789_, 1, v___x_6788_);
    v___x_6790_ = l_Lean_Elab_TermInfo_format___lam__0___closed__1;
    v___x_6791_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6791_, 0, v___x_6789_);
    lean_ctor_set(v___x_6791_, 1, v___x_6790_);
    v___x_6792_ = l_Lean_Name_toString(v_id_6782_, v___x_6786_);
    v___x_6793_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6793_, 0, v___x_6792_);
    v___x_6794_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6794_, 0, v___x_6791_);
    lean_ctor_set(v___x_6794_, 1, v___x_6793_);
    v___x_6795_ = l_Lean_Elab_FVarAliasInfo_format___closed__3;
    v___x_6796_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6796_, 0, v___x_6794_);
    lean_ctor_set(v___x_6796_, 1, v___x_6795_);
    v___x_6797_ = l_Lean_Name_toString(v_baseId_6783_, v___x_6786_);
    v___x_6798_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6798_, 0, v___x_6797_);
    v___x_6799_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6799_, 0, v___x_6796_);
    lean_ctor_set(v___x_6799_, 1, v___x_6798_);
    return v___x_6799_;
}
pub unsafe fn l_Lean_Elab_FieldRedeclInfo_format(
    mut v_ctx_6803_: *mut LeanObject,
    mut v_info_6804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    v___x_6805_ = l_Lean_Elab_FieldRedeclInfo_format___closed__1;
    v___x_6806_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_6803_, v_info_6804_);
    v___x_6807_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6807_, 0, v___x_6805_);
    lean_ctor_set(v___x_6807_, 1, v___x_6806_);
    return v___x_6807_;
}
pub unsafe fn l_Lean_Elab_FieldRedeclInfo_format___boxed(
    mut v_ctx_6808_: *mut LeanObject,
    mut v_info_6809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6810_: *mut LeanObject = core::ptr::null_mut();
    v_res_6810_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_6808_, v_info_6809_);
    lean_dec(v_info_6809_);
    return v_res_6810_;
}
pub unsafe fn l_Lean_Elab_DelabTermInfo_docString_x3f(
    mut v_ppCtx_6813_: *mut LeanObject,
    mut v_info_6814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mkDocString_x3f_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6822_: u8 = 0;
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6827_: u8 = 0;
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6834_: u8 = 0;
    let mut v_a_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6838_: u8 = 0;
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6850_: u8 = 0;
    let mut v_isSharedCheck_6851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mkDocString_x3f_6816_ = lean_ctor_get(v_info_6814_, 2);
                lean_inc(v_mkDocString_x3f_6816_);
                lean_dec_ref(v_info_6814_);
                if lean_obj_tag(v_mkDocString_x3f_6816_) == 0 {
                    lean_dec_ref(v_ppCtx_6813_);
                    v___x_6817_ = lean_box(0);
                    v___x_6818_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6818_, 0, v___x_6817_);
                    return v___x_6818_;
                } else {
                    v_val_6819_ = lean_ctor_get(v_mkDocString_x3f_6816_, 0);
                    v_isSharedCheck_6851_ = (!lean_is_exclusive(v_mkDocString_x3f_6816_)) as u8;
                    if v_isSharedCheck_6851_ == 0 {
                        v___x_6821_ = v_mkDocString_x3f_6816_;
                        v_isShared_6822_ = v_isSharedCheck_6851_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6819_);
                        lean_dec(v_mkDocString_x3f_6816_);
                        v___x_6821_ = lean_box(0);
                        v_isShared_6822_ = v_isSharedCheck_6851_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6823_ = lean_apply_2(v_val_6819_, v_ppCtx_6813_, lean_box(0));
                if lean_obj_tag(v___x_6823_) == 0 {
                    v_a_6824_ = lean_ctor_get(v___x_6823_, 0);
                    v_isSharedCheck_6834_ = (!lean_is_exclusive(v___x_6823_)) as u8;
                    if v_isSharedCheck_6834_ == 0 {
                        v___x_6826_ = v___x_6823_;
                        v_isShared_6827_ = v_isSharedCheck_6834_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6824_);
                        lean_dec(v___x_6823_);
                        v___x_6826_ = lean_box(0);
                        v_isShared_6827_ = v_isSharedCheck_6834_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6835_ = lean_ctor_get(v___x_6823_, 0);
                    v_isSharedCheck_6850_ = (!lean_is_exclusive(v___x_6823_)) as u8;
                    if v_isSharedCheck_6850_ == 0 {
                        v___x_6837_ = v___x_6823_;
                        v_isShared_6838_ = v_isSharedCheck_6850_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6835_);
                        lean_dec(v___x_6823_);
                        v___x_6837_ = lean_box(0);
                        v_isShared_6838_ = v_isSharedCheck_6850_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6822_ == 0 {
                    lean_ctor_set(v___x_6821_, 0, v_a_6824_);
                    v___x_6829_ = v___x_6821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6824_);
                    v___x_6829_ = v_reuseFailAlloc_6833_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6827_ == 0 {
                    lean_ctor_set(v___x_6826_, 0, v___x_6829_);
                    v___x_6831_ = v___x_6826_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6832_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6832_, 0, v___x_6829_);
                    v___x_6831_ = v_reuseFailAlloc_6832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6831_;
            }
            5 => {
                v___x_6839_ = l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0;
                v___x_6840_ = lean_io_error_to_string(v_a_6835_);
                v___x_6841_ = lean_string_append(v___x_6839_, v___x_6840_);
                lean_dec_ref(v___x_6840_);
                v___x_6842_ = l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1;
                v___x_6843_ = lean_string_append(v___x_6841_, v___x_6842_);
                if v_isShared_6822_ == 0 {
                    lean_ctor_set(v___x_6821_, 0, v___x_6843_);
                    v___x_6845_ = v___x_6821_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6849_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6849_, 0, v___x_6843_);
                    v___x_6845_ = v_reuseFailAlloc_6849_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6838_ == 0 {
                    lean_ctor_set_tag(v___x_6837_, 0);
                    lean_ctor_set(v___x_6837_, 0, v___x_6845_);
                    v___x_6847_ = v___x_6837_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6848_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6848_, 0, v___x_6845_);
                    v___x_6847_ = v_reuseFailAlloc_6848_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(
    mut v_ppCtx_6852_: *mut LeanObject,
    mut v_info_6853_: *mut LeanObject,
    mut v_a_6854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6855_: *mut LeanObject = core::ptr::null_mut();
    v_res_6855_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_6852_, v_info_6853_);
    return v_res_6855_;
}
pub unsafe fn l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(
    mut v_x_6856_: *mut LeanObject,
    mut v_x_6857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6862_: u8 = 0;
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6856_) == 0 {
                    v___x_6858_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1;
                    return v___x_6858_;
                } else {
                    v_val_6859_ = lean_ctor_get(v_x_6856_, 0);
                    v_isSharedCheck_6870_ = (!lean_is_exclusive(v_x_6856_)) as u8;
                    if v_isSharedCheck_6870_ == 0 {
                        v___x_6861_ = v_x_6856_;
                        v_isShared_6862_ = v_isSharedCheck_6870_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6859_);
                        lean_dec(v_x_6856_);
                        v___x_6861_ = lean_box(0);
                        v_isShared_6862_ = v_isSharedCheck_6870_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6863_ =
                    l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3;
                v___x_6864_ = l_String_quote(v_val_6859_);
                if v_isShared_6862_ == 0 {
                    lean_ctor_set_tag(v___x_6861_, 3);
                    lean_ctor_set(v___x_6861_, 0, v___x_6864_);
                    v___x_6866_ = v___x_6861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6869_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6869_, 0, v___x_6864_);
                    v___x_6866_ = v_reuseFailAlloc_6869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6867_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6867_, 0, v___x_6863_);
                lean_ctor_set(v___x_6867_, 1, v___x_6866_);
                v___x_6868_ = l_Repr_addAppParen(v___x_6867_, v_x_6857_);
                return v___x_6868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(
    mut v_x_6871_: *mut LeanObject,
    mut v_x_6872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6873_: *mut LeanObject = core::ptr::null_mut();
    v_res_6873_ =
        l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_6871_, v_x_6872_);
    lean_dec(v_x_6872_);
    return v_res_6873_;
}
pub unsafe fn l_Lean_Elab_DelabTermInfo_format(
    mut v_ctx_6888_: *mut LeanObject,
    mut v_info_6889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toTermInfo_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_location_x3f_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_explicit_6899_: u8 = 0;
    let mut v___y_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6925_: u8 = 0;
    let mut v_range_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6932_: u8 = 0;
    let mut v_line_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6937_: u8 = 0;
    let mut v_line_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6942_: u8 = 0;
    let mut v___x_6943_: u8 = 0;
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6979_: u8 = 0;
    let mut v_isSharedCheck_6980_: u8 = 0;
    let mut v_isSharedCheck_6981_: u8 = 0;
    let mut v_unused_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6983_: u8 = 0;
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toTermInfo_6897_ = lean_ctor_get(v_info_6889_, 0);
                lean_inc_ref(v_toTermInfo_6897_);
                v_location_x3f_6898_ = lean_ctor_get(v_info_6889_, 1);
                lean_inc(v_location_x3f_6898_);
                v_explicit_6899_ = lean_ctor_get_uint8(
                    v_info_6889_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if lean_obj_tag(v_location_x3f_6898_) == 1 {
                    v_val_6922_ = lean_ctor_get(v_location_x3f_6898_, 0);
                    v_isSharedCheck_6983_ = (!lean_is_exclusive(v_location_x3f_6898_)) as u8;
                    if v_isSharedCheck_6983_ == 0 {
                        v___x_6924_ = v_location_x3f_6898_;
                        v_isShared_6925_ = v_isSharedCheck_6983_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_6922_);
                        lean_dec(v_location_x3f_6898_);
                        v___x_6924_ = lean_box(0);
                        v_isShared_6925_ = v_isSharedCheck_6983_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_location_x3f_6898_);
                    v___x_6984_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1;
                    v___y_6901_ = v___x_6984_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v___y_6893_);
                v___x_6894_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6894_, 0, v___y_6893_);
                v___x_6895_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6895_, 0, v___y_6892_);
                lean_ctor_set(v___x_6895_, 1, v___x_6894_);
                v___x_6896_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6896_, 0, v___x_6895_);
                return v___x_6896_;
            }
            2 => {
                v_lctx_6902_ = lean_ctor_get(v_toTermInfo_6897_, 1);
                lean_inc_ref(v_lctx_6902_);
                v___x_6903_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_6888_, v_lctx_6902_);
                v___x_6904_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_6903_, v_info_6889_);
                v_a_6905_ = lean_ctor_get(v___x_6904_, 0);
                lean_inc(v_a_6905_);
                lean_dec_ref(v___x_6904_);
                v___x_6906_ = l_Lean_Elab_TermInfo_format(v_ctx_6888_, v_toTermInfo_6897_);
                if lean_obj_tag(v___x_6906_) == 0 {
                    v_a_6907_ = lean_ctor_get(v___x_6906_, 0);
                    lean_inc(v_a_6907_);
                    lean_dec_ref_known(v___x_6906_, 1);
                    v___x_6908_ = l_Lean_Elab_DelabTermInfo_format___closed__1;
                    v___x_6909_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6909_, 0, v___x_6908_);
                    lean_ctor_set(v___x_6909_, 1, v_a_6907_);
                    v___x_6910_ = l_Lean_Elab_DelabTermInfo_format___closed__3;
                    v___x_6911_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6911_, 0, v___x_6909_);
                    lean_ctor_set(v___x_6911_, 1, v___x_6910_);
                    v___x_6912_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6912_, 0, v___x_6911_);
                    lean_ctor_set(v___x_6912_, 1, v___y_6901_);
                    v___x_6913_ = l_Lean_Elab_DelabTermInfo_format___closed__5;
                    v___x_6914_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6914_, 0, v___x_6912_);
                    lean_ctor_set(v___x_6914_, 1, v___x_6913_);
                    v___x_6915_ = lean_unsigned_to_nat(0);
                    v___x_6916_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(
                        v_a_6905_,
                        v___x_6915_,
                    );
                    v___x_6917_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6917_, 0, v___x_6914_);
                    lean_ctor_set(v___x_6917_, 1, v___x_6916_);
                    v___x_6918_ = l_Lean_Elab_DelabTermInfo_format___closed__7;
                    v___x_6919_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_6919_, 0, v___x_6917_);
                    lean_ctor_set(v___x_6919_, 1, v___x_6918_);
                    if v_explicit_6899_ == 0 {
                        v___x_6920_ = l_Lean_Elab_DelabTermInfo_format___closed__8;
                        v___y_6892_ = v___x_6919_;
                        v___y_6893_ = v___x_6920_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6921_ = l_Lean_Elab_DelabTermInfo_format___closed__9;
                        v___y_6892_ = v___x_6919_;
                        v___y_6893_ = v___x_6921_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6905_);
                    lean_dec(v___y_6901_);
                    return v___x_6906_;
                }
            }
            3 => {
                v_range_6926_ = lean_ctor_get(v_val_6922_, 1);
                v_pos_6927_ = lean_ctor_get(v_range_6926_, 0);
                lean_inc_ref(v_pos_6927_);
                v_endPos_6928_ = lean_ctor_get(v_range_6926_, 2);
                lean_inc_ref(v_endPos_6928_);
                v_module_6929_ = lean_ctor_get(v_val_6922_, 0);
                v_isSharedCheck_6981_ = (!lean_is_exclusive(v_val_6922_)) as u8;
                if v_isSharedCheck_6981_ == 0 {
                    v_unused_6982_ = lean_ctor_get(v_val_6922_, 1);
                    lean_dec(v_unused_6982_);
                    v___x_6931_ = v_val_6922_;
                    v_isShared_6932_ = v_isSharedCheck_6981_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_module_6929_);
                    lean_dec(v_val_6922_);
                    v___x_6931_ = lean_box(0);
                    v_isShared_6932_ = v_isSharedCheck_6981_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_line_6933_ = lean_ctor_get(v_pos_6927_, 0);
                v_column_6934_ = lean_ctor_get(v_pos_6927_, 1);
                v_isSharedCheck_6980_ = (!lean_is_exclusive(v_pos_6927_)) as u8;
                if v_isSharedCheck_6980_ == 0 {
                    v___x_6936_ = v_pos_6927_;
                    v_isShared_6937_ = v_isSharedCheck_6980_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_column_6934_);
                    lean_inc(v_line_6933_);
                    lean_dec(v_pos_6927_);
                    v___x_6936_ = lean_box(0);
                    v_isShared_6937_ = v_isSharedCheck_6980_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_line_6938_ = lean_ctor_get(v_endPos_6928_, 0);
                v_column_6939_ = lean_ctor_get(v_endPos_6928_, 1);
                v_isSharedCheck_6979_ = (!lean_is_exclusive(v_endPos_6928_)) as u8;
                if v_isSharedCheck_6979_ == 0 {
                    v___x_6941_ = v_endPos_6928_;
                    v_isShared_6942_ = v_isSharedCheck_6979_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_column_6939_);
                    lean_inc(v_line_6938_);
                    lean_dec(v_endPos_6928_);
                    v___x_6941_ = lean_box(0);
                    v_isShared_6942_ = v_isSharedCheck_6979_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6943_ = 1;
                v___x_6944_ = l_Lean_Name_toString(v_module_6929_, v___x_6943_);
                if v_isShared_6925_ == 0 {
                    lean_ctor_set_tag(v___x_6924_, 3);
                    lean_ctor_set(v___x_6924_, 0, v___x_6944_);
                    v___x_6946_ = v___x_6924_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6978_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6978_, 0, v___x_6944_);
                    v___x_6946_ = v_reuseFailAlloc_6978_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6947_ = l_Lean_Elab_TermInfo_format___lam__0___closed__5;
                if v_isShared_6942_ == 0 {
                    lean_ctor_set_tag(v___x_6941_, 5);
                    lean_ctor_set(v___x_6941_, 1, v___x_6947_);
                    lean_ctor_set(v___x_6941_, 0, v___x_6946_);
                    v___x_6949_ = v___x_6941_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6977_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6977_, 0, v___x_6946_);
                    lean_ctor_set(v_reuseFailAlloc_6977_, 1, v___x_6947_);
                    v___x_6949_ = v_reuseFailAlloc_6977_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6950_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1;
                v___x_6951_ = l_Nat_reprFast(v_line_6933_);
                v___x_6952_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6952_, 0, v___x_6951_);
                if v_isShared_6937_ == 0 {
                    lean_ctor_set_tag(v___x_6936_, 5);
                    lean_ctor_set(v___x_6936_, 1, v___x_6952_);
                    lean_ctor_set(v___x_6936_, 0, v___x_6950_);
                    v___x_6954_ = v___x_6936_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6976_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6976_, 0, v___x_6950_);
                    lean_ctor_set(v_reuseFailAlloc_6976_, 1, v___x_6952_);
                    v___x_6954_ = v_reuseFailAlloc_6976_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6955_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3;
                if v_isShared_6932_ == 0 {
                    lean_ctor_set_tag(v___x_6931_, 5);
                    lean_ctor_set(v___x_6931_, 1, v___x_6955_);
                    lean_ctor_set(v___x_6931_, 0, v___x_6954_);
                    v___x_6957_ = v___x_6931_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6975_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6975_, 0, v___x_6954_);
                    lean_ctor_set(v_reuseFailAlloc_6975_, 1, v___x_6955_);
                    v___x_6957_ = v_reuseFailAlloc_6975_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_6958_ = l_Nat_reprFast(v_column_6934_);
                v___x_6959_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6959_, 0, v___x_6958_);
                v___x_6960_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6960_, 0, v___x_6957_);
                lean_ctor_set(v___x_6960_, 1, v___x_6959_);
                v___x_6961_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5;
                v___x_6962_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6962_, 0, v___x_6960_);
                lean_ctor_set(v___x_6962_, 1, v___x_6961_);
                v___x_6963_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6963_, 0, v___x_6949_);
                lean_ctor_set(v___x_6963_, 1, v___x_6962_);
                v___x_6964_ =
                    l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1;
                v___x_6965_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6965_, 0, v___x_6963_);
                lean_ctor_set(v___x_6965_, 1, v___x_6964_);
                v___x_6966_ = l_Nat_reprFast(v_line_6938_);
                v___x_6967_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6967_, 0, v___x_6966_);
                v___x_6968_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6968_, 0, v___x_6950_);
                lean_ctor_set(v___x_6968_, 1, v___x_6967_);
                v___x_6969_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6969_, 0, v___x_6968_);
                lean_ctor_set(v___x_6969_, 1, v___x_6955_);
                v___x_6970_ = l_Nat_reprFast(v_column_6939_);
                v___x_6971_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6971_, 0, v___x_6970_);
                v___x_6972_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6972_, 0, v___x_6969_);
                lean_ctor_set(v___x_6972_, 1, v___x_6971_);
                v___x_6973_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6973_, 0, v___x_6972_);
                lean_ctor_set(v___x_6973_, 1, v___x_6961_);
                v___x_6974_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6974_, 0, v___x_6965_);
                lean_ctor_set(v___x_6974_, 1, v___x_6973_);
                v___y_6901_ = v___x_6974_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_DelabTermInfo_format___boxed(
    mut v_ctx_6985_: *mut LeanObject,
    mut v_info_6986_: *mut LeanObject,
    mut v_a_6987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6988_: *mut LeanObject = core::ptr::null_mut();
    v_res_6988_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_6985_, v_info_6986_);
    return v_res_6988_;
}
pub unsafe fn l_Lean_Elab_ChoiceInfo_format(
    mut v_ctx_6992_: *mut LeanObject,
    mut v_info_6993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    v___x_6994_ = l_Lean_Elab_ChoiceInfo_format___closed__1;
    v___x_6995_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_6992_, v_info_6993_);
    v___x_6996_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_6996_, 0, v___x_6994_);
    lean_ctor_set(v___x_6996_, 1, v___x_6995_);
    return v___x_6996_;
}
pub unsafe fn l_Lean_Elab_DocInfo_format(
    mut v_ctx_7000_: *mut LeanObject,
    mut v_info_7001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stx_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: u8 = 0;
    let mut v___x_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    v_stx_7002_ = lean_ctor_get(v_info_7001_, 1);
    v___x_7003_ = l_Lean_Elab_DocInfo_format___closed__1;
    lean_inc(v_stx_7002_);
    v___x_7004_ = l_Lean_Syntax_getKind(v_stx_7002_);
    v___x_7005_ = 1;
    v___x_7006_ = l_Lean_Name_toString(v___x_7004_, v___x_7005_);
    v___x_7007_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_7007_, 0, v___x_7006_);
    v___x_7008_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7008_, 0, v___x_7003_);
    lean_ctor_set(v___x_7008_, 1, v___x_7007_);
    v___x_7009_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1;
    v___x_7010_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7010_, 0, v___x_7008_);
    lean_ctor_set(v___x_7010_, 1, v___x_7009_);
    v___x_7011_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_7000_, v_info_7001_);
    v___x_7012_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7012_, 0, v___x_7010_);
    lean_ctor_set(v___x_7012_, 1, v___x_7011_);
    return v___x_7012_;
}
pub unsafe fn l_Lean_Elab_DocElabInfo_format(
    mut v_ctx_7022_: *mut LeanObject,
    mut v_info_7023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toElabInfo_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_7026_: u8 = 0;
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: u8 = 0;
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    v_toElabInfo_7024_ = lean_ctor_get(v_info_7023_, 0);
    lean_inc_ref(v_toElabInfo_7024_);
    v_name_7025_ = lean_ctor_get(v_info_7023_, 1);
    lean_inc(v_name_7025_);
    v_kind_7026_ = lean_ctor_get_uint8(
        v_info_7023_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec_ref(v_info_7023_);
    v___x_7027_ = l_Lean_Elab_DocElabInfo_format___closed__1;
    v___x_7028_ = 1;
    v___x_7029_ = l_Lean_Name_toString(v_name_7025_, v___x_7028_);
    v___x_7030_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_7030_, 0, v___x_7029_);
    v___x_7031_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7031_, 0, v___x_7027_);
    lean_ctor_set(v___x_7031_, 1, v___x_7030_);
    v___x_7032_ = l_Lean_Elab_DocElabInfo_format___closed__3;
    v___x_7033_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7033_, 0, v___x_7031_);
    lean_ctor_set(v___x_7033_, 1, v___x_7032_);
    v___x_7034_ = lean_unsigned_to_nat(0);
    v___x_7035_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_7026_, v___x_7034_);
    v___x_7036_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7036_, 0, v___x_7033_);
    lean_ctor_set(v___x_7036_, 1, v___x_7035_);
    v___x_7037_ = l_Lean_Elab_DocElabInfo_format___closed__5;
    v___x_7038_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7038_, 0, v___x_7036_);
    lean_ctor_set(v___x_7038_, 1, v___x_7037_);
    v___x_7039_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(
        v_ctx_7022_,
        v_toElabInfo_7024_,
    );
    v___x_7040_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_7040_, 0, v___x_7038_);
    lean_ctor_set(v___x_7040_, 1, v___x_7039_);
    return v___x_7040_;
}
pub unsafe fn l_Lean_Elab_Info_format(
    mut v_ctx_7041_: *mut LeanObject,
    mut v_x_7042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7051_: u8 = 0;
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7056_: u8 = 0;
    let mut v_i_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7072_: u8 = 0;
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7077_: u8 = 0;
    let mut v_i_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7081_: u8 = 0;
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7086_: u8 = 0;
    let mut v_i_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7090_: u8 = 0;
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7095_: u8 = 0;
    let mut v_i_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7099_: u8 = 0;
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7104_: u8 = 0;
    let mut v_i_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7110_: u8 = 0;
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7115_: u8 = 0;
    let mut v_i_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7119_: u8 = 0;
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7124_: u8 = 0;
    let mut v_i_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7128_: u8 = 0;
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_7042_) {
                0 => {
                    v_i_7044_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7044_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7045_ = l_Lean_Elab_TacticInfo_format(v_ctx_7041_, v_i_7044_);
                    return v___x_7045_;
                }
                1 => {
                    v_i_7046_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7046_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7047_ = l_Lean_Elab_TermInfo_format(v_ctx_7041_, v_i_7046_);
                    return v___x_7047_;
                }
                2 => {
                    v_i_7048_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7056_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7056_ == 0 {
                        v___x_7050_ = v_x_7042_;
                        v_isShared_7051_ = v_isSharedCheck_7056_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_i_7048_);
                        lean_dec(v_x_7042_);
                        v___x_7050_ = lean_box(0);
                        v_isShared_7051_ = v_isSharedCheck_7056_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_i_7057_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7057_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7058_ = l_Lean_Elab_CommandInfo_format(v_ctx_7041_, v_i_7057_);
                    return v___x_7058_;
                }
                4 => {
                    v_i_7059_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7059_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7060_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_7041_, v_i_7059_);
                    lean_dec_ref(v_ctx_7041_);
                    return v___x_7060_;
                }
                5 => {
                    v_i_7061_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7061_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7062_ = l_Lean_Elab_OptionInfo_format(v_ctx_7041_, v_i_7061_);
                    return v___x_7062_;
                }
                6 => {
                    v_i_7063_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7063_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7064_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_7041_, v_i_7063_);
                    return v___x_7064_;
                }
                7 => {
                    v_i_7065_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7065_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7066_ = l_Lean_Elab_FieldInfo_format(v_ctx_7041_, v_i_7065_);
                    return v___x_7066_;
                }
                8 => {
                    v_i_7067_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7067_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7068_ = l_Lean_Elab_CompletionInfo_format(v_ctx_7041_, v_i_7067_);
                    return v___x_7068_;
                }
                9 => {
                    lean_dec_ref(v_ctx_7041_);
                    v_i_7069_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7077_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7077_ == 0 {
                        v___x_7071_ = v_x_7042_;
                        v_isShared_7072_ = v_isSharedCheck_7077_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_i_7069_);
                        lean_dec(v_x_7042_);
                        v___x_7071_ = lean_box(0);
                        v_isShared_7072_ = v_isSharedCheck_7077_;
                        state = 3;
                        continue;
                    }
                }
                10 => {
                    lean_dec_ref(v_ctx_7041_);
                    v_i_7078_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7086_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7086_ == 0 {
                        v___x_7080_ = v_x_7042_;
                        v_isShared_7081_ = v_isSharedCheck_7086_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_i_7078_);
                        lean_dec(v_x_7042_);
                        v___x_7080_ = lean_box(0);
                        v_isShared_7081_ = v_isSharedCheck_7086_;
                        state = 5;
                        continue;
                    }
                }
                11 => {
                    lean_dec_ref(v_ctx_7041_);
                    v_i_7087_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7095_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7095_ == 0 {
                        v___x_7089_ = v_x_7042_;
                        v_isShared_7090_ = v_isSharedCheck_7095_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_i_7087_);
                        lean_dec(v_x_7042_);
                        v___x_7089_ = lean_box(0);
                        v_isShared_7090_ = v_isSharedCheck_7095_;
                        state = 7;
                        continue;
                    }
                }
                12 => {
                    v_i_7096_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7104_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7104_ == 0 {
                        v___x_7098_ = v_x_7042_;
                        v_isShared_7099_ = v_isSharedCheck_7104_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_i_7096_);
                        lean_dec(v_x_7042_);
                        v___x_7098_ = lean_box(0);
                        v_isShared_7099_ = v_isSharedCheck_7104_;
                        state = 9;
                        continue;
                    }
                }
                13 => {
                    v_i_7105_ = lean_ctor_get(v_x_7042_, 0);
                    lean_inc_ref(v_i_7105_);
                    lean_dec_ref_known(v_x_7042_, 1);
                    v___x_7106_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_7041_, v_i_7105_);
                    return v___x_7106_;
                }
                14 => {
                    v_i_7107_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7115_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7115_ == 0 {
                        v___x_7109_ = v_x_7042_;
                        v_isShared_7110_ = v_isSharedCheck_7115_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_i_7107_);
                        lean_dec(v_x_7042_);
                        v___x_7109_ = lean_box(0);
                        v_isShared_7110_ = v_isSharedCheck_7115_;
                        state = 11;
                        continue;
                    }
                }
                15 => {
                    v_i_7116_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7124_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7124_ == 0 {
                        v___x_7118_ = v_x_7042_;
                        v_isShared_7119_ = v_isSharedCheck_7124_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_i_7116_);
                        lean_dec(v_x_7042_);
                        v___x_7118_ = lean_box(0);
                        v_isShared_7119_ = v_isSharedCheck_7124_;
                        state = 13;
                        continue;
                    }
                }
                _ => {
                    v_i_7125_ = lean_ctor_get(v_x_7042_, 0);
                    v_isSharedCheck_7133_ = (!lean_is_exclusive(v_x_7042_)) as u8;
                    if v_isSharedCheck_7133_ == 0 {
                        v___x_7127_ = v_x_7042_;
                        v_isShared_7128_ = v_isSharedCheck_7133_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_i_7125_);
                        lean_dec(v_x_7042_);
                        v___x_7127_ = lean_box(0);
                        v_isShared_7128_ = v_isSharedCheck_7133_;
                        state = 15;
                        continue;
                    }
                }
            },
            1 => {
                v___x_7052_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_7041_, v_i_7048_);
                if v_isShared_7051_ == 0 {
                    lean_ctor_set_tag(v___x_7050_, 0);
                    lean_ctor_set(v___x_7050_, 0, v___x_7052_);
                    v___x_7054_ = v___x_7050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7055_, 0, v___x_7052_);
                    v___x_7054_ = v_reuseFailAlloc_7055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7054_;
            }
            3 => {
                v___x_7073_ = l_Lean_Elab_UserWidgetInfo_format(v_i_7069_);
                if v_isShared_7072_ == 0 {
                    lean_ctor_set_tag(v___x_7071_, 0);
                    lean_ctor_set(v___x_7071_, 0, v___x_7073_);
                    v___x_7075_ = v___x_7071_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7076_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7076_, 0, v___x_7073_);
                    v___x_7075_ = v_reuseFailAlloc_7076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7075_;
            }
            5 => {
                v___x_7082_ = l_Lean_Elab_CustomInfo_format(v_i_7078_);
                if v_isShared_7081_ == 0 {
                    lean_ctor_set_tag(v___x_7080_, 0);
                    lean_ctor_set(v___x_7080_, 0, v___x_7082_);
                    v___x_7084_ = v___x_7080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7085_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7085_, 0, v___x_7082_);
                    v___x_7084_ = v_reuseFailAlloc_7085_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7084_;
            }
            7 => {
                v___x_7091_ = l_Lean_Elab_FVarAliasInfo_format(v_i_7087_);
                if v_isShared_7090_ == 0 {
                    lean_ctor_set_tag(v___x_7089_, 0);
                    lean_ctor_set(v___x_7089_, 0, v___x_7091_);
                    v___x_7093_ = v___x_7089_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7094_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7094_, 0, v___x_7091_);
                    v___x_7093_ = v_reuseFailAlloc_7094_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7093_;
            }
            9 => {
                v___x_7100_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_7041_, v_i_7096_);
                lean_dec(v_i_7096_);
                if v_isShared_7099_ == 0 {
                    lean_ctor_set_tag(v___x_7098_, 0);
                    lean_ctor_set(v___x_7098_, 0, v___x_7100_);
                    v___x_7102_ = v___x_7098_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7103_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7103_, 0, v___x_7100_);
                    v___x_7102_ = v_reuseFailAlloc_7103_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7102_;
            }
            11 => {
                v___x_7111_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_7041_, v_i_7107_);
                if v_isShared_7110_ == 0 {
                    lean_ctor_set_tag(v___x_7109_, 0);
                    lean_ctor_set(v___x_7109_, 0, v___x_7111_);
                    v___x_7113_ = v___x_7109_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7114_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7114_, 0, v___x_7111_);
                    v___x_7113_ = v_reuseFailAlloc_7114_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7113_;
            }
            13 => {
                v___x_7120_ = l_Lean_Elab_DocInfo_format(v_ctx_7041_, v_i_7116_);
                if v_isShared_7119_ == 0 {
                    lean_ctor_set_tag(v___x_7118_, 0);
                    lean_ctor_set(v___x_7118_, 0, v___x_7120_);
                    v___x_7122_ = v___x_7118_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7123_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7123_, 0, v___x_7120_);
                    v___x_7122_ = v_reuseFailAlloc_7123_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7122_;
            }
            15 => {
                v___x_7129_ = l_Lean_Elab_DocElabInfo_format(v_ctx_7041_, v_i_7125_);
                if v_isShared_7128_ == 0 {
                    lean_ctor_set_tag(v___x_7127_, 0);
                    lean_ctor_set(v___x_7127_, 0, v___x_7129_);
                    v___x_7131_ = v___x_7127_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7132_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7132_, 0, v___x_7129_);
                    v___x_7131_ = v_reuseFailAlloc_7132_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_format___boxed(
    mut v_ctx_7134_: *mut LeanObject,
    mut v_x_7135_: *mut LeanObject,
    mut v_a_7136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7137_: *mut LeanObject = core::ptr::null_mut();
    v_res_7137_ = l_Lean_Elab_Info_format(v_ctx_7134_, v_x_7135_);
    return v_res_7137_;
}
pub unsafe fn l_Lean_Elab_Info_toElabInfo_x3f(mut v_x_7138_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7142_: u8 = 0;
    let mut v_toElabInfo_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7147_: u8 = 0;
    let mut v_i_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7151_: u8 = 0;
    let mut v_toElabInfo_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7156_: u8 = 0;
    let mut v_i_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7160_: u8 = 0;
    let mut v_toElabInfo_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7165_: u8 = 0;
    let mut v_i_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7169_: u8 = 0;
    let mut v___x_7171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7173_: u8 = 0;
    let mut v_i_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7177_: u8 = 0;
    let mut v_toTermInfo_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7183_: u8 = 0;
    let mut v_i_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7187_: u8 = 0;
    let mut v___x_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7191_: u8 = 0;
    let mut v_i_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7195_: u8 = 0;
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7199_: u8 = 0;
    let mut v_i_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7203_: u8 = 0;
    let mut v_toElabInfo_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7208_: u8 = 0;
    let mut v___x_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_7138_) {
                0 => {
                    v_i_7139_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7147_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7147_ == 0 {
                        v___x_7141_ = v_x_7138_;
                        v_isShared_7142_ = v_isSharedCheck_7147_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_i_7139_);
                        lean_dec(v_x_7138_);
                        v___x_7141_ = lean_box(0);
                        v_isShared_7142_ = v_isSharedCheck_7147_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_7148_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7156_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7156_ == 0 {
                        v___x_7150_ = v_x_7138_;
                        v_isShared_7151_ = v_isSharedCheck_7156_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_i_7148_);
                        lean_dec(v_x_7138_);
                        v___x_7150_ = lean_box(0);
                        v_isShared_7151_ = v_isSharedCheck_7156_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_i_7157_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7165_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7165_ == 0 {
                        v___x_7159_ = v_x_7138_;
                        v_isShared_7160_ = v_isSharedCheck_7165_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_i_7157_);
                        lean_dec(v_x_7138_);
                        v___x_7159_ = lean_box(0);
                        v_isShared_7160_ = v_isSharedCheck_7165_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_i_7166_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7173_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7173_ == 0 {
                        v___x_7168_ = v_x_7138_;
                        v_isShared_7169_ = v_isSharedCheck_7173_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_i_7166_);
                        lean_dec(v_x_7138_);
                        v___x_7168_ = lean_box(0);
                        v_isShared_7169_ = v_isSharedCheck_7173_;
                        state = 7;
                        continue;
                    }
                }
                13 => {
                    v_i_7174_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7183_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7183_ == 0 {
                        v___x_7176_ = v_x_7138_;
                        v_isShared_7177_ = v_isSharedCheck_7183_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_i_7174_);
                        lean_dec(v_x_7138_);
                        v___x_7176_ = lean_box(0);
                        v_isShared_7177_ = v_isSharedCheck_7183_;
                        state = 9;
                        continue;
                    }
                }
                14 => {
                    v_i_7184_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7191_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7191_ == 0 {
                        v___x_7186_ = v_x_7138_;
                        v_isShared_7187_ = v_isSharedCheck_7191_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_i_7184_);
                        lean_dec(v_x_7138_);
                        v___x_7186_ = lean_box(0);
                        v_isShared_7187_ = v_isSharedCheck_7191_;
                        state = 11;
                        continue;
                    }
                }
                15 => {
                    v_i_7192_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7199_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7199_ == 0 {
                        v___x_7194_ = v_x_7138_;
                        v_isShared_7195_ = v_isSharedCheck_7199_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_i_7192_);
                        lean_dec(v_x_7138_);
                        v___x_7194_ = lean_box(0);
                        v_isShared_7195_ = v_isSharedCheck_7199_;
                        state = 13;
                        continue;
                    }
                }
                16 => {
                    v_i_7200_ = lean_ctor_get(v_x_7138_, 0);
                    v_isSharedCheck_7208_ = (!lean_is_exclusive(v_x_7138_)) as u8;
                    if v_isSharedCheck_7208_ == 0 {
                        v___x_7202_ = v_x_7138_;
                        v_isShared_7203_ = v_isSharedCheck_7208_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_i_7200_);
                        lean_dec(v_x_7138_);
                        v___x_7202_ = lean_box(0);
                        v_isShared_7203_ = v_isSharedCheck_7208_;
                        state = 15;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_x_7138_);
                    v___x_7209_ = lean_box(0);
                    return v___x_7209_;
                }
            },
            1 => {
                v_toElabInfo_7143_ = lean_ctor_get(v_i_7139_, 0);
                lean_inc_ref(v_toElabInfo_7143_);
                lean_dec_ref(v_i_7139_);
                if v_isShared_7142_ == 0 {
                    lean_ctor_set_tag(v___x_7141_, 1);
                    lean_ctor_set(v___x_7141_, 0, v_toElabInfo_7143_);
                    v___x_7145_ = v___x_7141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7146_, 0, v_toElabInfo_7143_);
                    v___x_7145_ = v_reuseFailAlloc_7146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7145_;
            }
            3 => {
                v_toElabInfo_7152_ = lean_ctor_get(v_i_7148_, 0);
                lean_inc_ref(v_toElabInfo_7152_);
                lean_dec_ref(v_i_7148_);
                if v_isShared_7151_ == 0 {
                    lean_ctor_set(v___x_7150_, 0, v_toElabInfo_7152_);
                    v___x_7154_ = v___x_7150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7155_, 0, v_toElabInfo_7152_);
                    v___x_7154_ = v_reuseFailAlloc_7155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7154_;
            }
            5 => {
                v_toElabInfo_7161_ = lean_ctor_get(v_i_7157_, 0);
                lean_inc_ref(v_toElabInfo_7161_);
                lean_dec_ref(v_i_7157_);
                if v_isShared_7160_ == 0 {
                    lean_ctor_set_tag(v___x_7159_, 1);
                    lean_ctor_set(v___x_7159_, 0, v_toElabInfo_7161_);
                    v___x_7163_ = v___x_7159_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7164_, 0, v_toElabInfo_7161_);
                    v___x_7163_ = v_reuseFailAlloc_7164_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7163_;
            }
            7 => {
                if v_isShared_7169_ == 0 {
                    lean_ctor_set_tag(v___x_7168_, 1);
                    v___x_7171_ = v___x_7168_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7172_, 0, v_i_7166_);
                    v___x_7171_ = v_reuseFailAlloc_7172_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7171_;
            }
            9 => {
                v_toTermInfo_7178_ = lean_ctor_get(v_i_7174_, 0);
                lean_inc_ref(v_toTermInfo_7178_);
                lean_dec_ref(v_i_7174_);
                v_toElabInfo_7179_ = lean_ctor_get(v_toTermInfo_7178_, 0);
                lean_inc_ref(v_toElabInfo_7179_);
                lean_dec_ref(v_toTermInfo_7178_);
                if v_isShared_7177_ == 0 {
                    lean_ctor_set_tag(v___x_7176_, 1);
                    lean_ctor_set(v___x_7176_, 0, v_toElabInfo_7179_);
                    v___x_7181_ = v___x_7176_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7182_, 0, v_toElabInfo_7179_);
                    v___x_7181_ = v_reuseFailAlloc_7182_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7181_;
            }
            11 => {
                if v_isShared_7187_ == 0 {
                    lean_ctor_set_tag(v___x_7186_, 1);
                    v___x_7189_ = v___x_7186_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7190_, 0, v_i_7184_);
                    v___x_7189_ = v_reuseFailAlloc_7190_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7189_;
            }
            13 => {
                if v_isShared_7195_ == 0 {
                    lean_ctor_set_tag(v___x_7194_, 1);
                    v___x_7197_ = v___x_7194_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7198_, 0, v_i_7192_);
                    v___x_7197_ = v_reuseFailAlloc_7198_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7197_;
            }
            15 => {
                v_toElabInfo_7204_ = lean_ctor_get(v_i_7200_, 0);
                lean_inc_ref(v_toElabInfo_7204_);
                lean_dec_ref(v_i_7200_);
                if v_isShared_7203_ == 0 {
                    lean_ctor_set_tag(v___x_7202_, 1);
                    lean_ctor_set(v___x_7202_, 0, v_toElabInfo_7204_);
                    v___x_7206_ = v___x_7202_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7207_, 0, v_toElabInfo_7204_);
                    v___x_7206_ = v_reuseFailAlloc_7207_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_updateContext_x3f(
    mut v_x_7210_: *mut LeanObject,
    mut v_x_7211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7215_: u8 = 0;
    let mut v_toCommandContextInfo_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_x3f_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_autoImplicits_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v_env_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdEnv_x3f_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7232_: u8 = 0;
    let mut v_mctxAfter_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7243_: u8 = 0;
    let mut v_unused_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7245_: u8 = 0;
    let mut v_unused_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7210_) == 1 {
                    if lean_obj_tag(v_x_7211_) == 0 {
                        v_val_7212_ = lean_ctor_get(v_x_7210_, 0);
                        v_isSharedCheck_7247_ = (!lean_is_exclusive(v_x_7210_)) as u8;
                        if v_isSharedCheck_7247_ == 0 {
                            v___x_7214_ = v_x_7210_;
                            v_isShared_7215_ = v_isSharedCheck_7247_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_7212_);
                            lean_dec(v_x_7210_);
                            v___x_7214_ = lean_box(0);
                            v_isShared_7215_ = v_isSharedCheck_7247_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v_x_7210_;
                    }
                } else {
                    return v_x_7210_;
                }
            }
            1 => {
                v_toCommandContextInfo_7216_ = lean_ctor_get(v_val_7212_, 0);
                lean_inc_ref(v_toCommandContextInfo_7216_);
                v_i_7217_ = lean_ctor_get(v_x_7211_, 0);
                v_parentDecl_x3f_7218_ = lean_ctor_get(v_val_7212_, 1);
                v_autoImplicits_7219_ = lean_ctor_get(v_val_7212_, 2);
                v_isSharedCheck_7245_ = (!lean_is_exclusive(v_val_7212_)) as u8;
                if v_isSharedCheck_7245_ == 0 {
                    v_unused_7246_ = lean_ctor_get(v_val_7212_, 0);
                    lean_dec(v_unused_7246_);
                    v___x_7221_ = v_val_7212_;
                    v_isShared_7222_ = v_isSharedCheck_7245_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_autoImplicits_7219_);
                    lean_inc(v_parentDecl_x3f_7218_);
                    lean_dec(v_val_7212_);
                    v___x_7221_ = lean_box(0);
                    v_isShared_7222_ = v_isSharedCheck_7245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_env_7223_ = lean_ctor_get(v_toCommandContextInfo_7216_, 0);
                v_cmdEnv_x3f_7224_ = lean_ctor_get(v_toCommandContextInfo_7216_, 1);
                v_fileMap_7225_ = lean_ctor_get(v_toCommandContextInfo_7216_, 2);
                v_options_7226_ = lean_ctor_get(v_toCommandContextInfo_7216_, 4);
                v_currNamespace_7227_ = lean_ctor_get(v_toCommandContextInfo_7216_, 5);
                v_openDecls_7228_ = lean_ctor_get(v_toCommandContextInfo_7216_, 6);
                v_ngen_7229_ = lean_ctor_get(v_toCommandContextInfo_7216_, 7);
                v_isSharedCheck_7243_ = (!lean_is_exclusive(v_toCommandContextInfo_7216_)) as u8;
                if v_isSharedCheck_7243_ == 0 {
                    v_unused_7244_ = lean_ctor_get(v_toCommandContextInfo_7216_, 3);
                    lean_dec(v_unused_7244_);
                    v___x_7231_ = v_toCommandContextInfo_7216_;
                    v_isShared_7232_ = v_isSharedCheck_7243_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_ngen_7229_);
                    lean_inc(v_openDecls_7228_);
                    lean_inc(v_currNamespace_7227_);
                    lean_inc(v_options_7226_);
                    lean_inc(v_fileMap_7225_);
                    lean_inc(v_cmdEnv_x3f_7224_);
                    lean_inc(v_env_7223_);
                    lean_dec(v_toCommandContextInfo_7216_);
                    v___x_7231_ = lean_box(0);
                    v_isShared_7232_ = v_isSharedCheck_7243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_mctxAfter_7233_ = lean_ctor_get(v_i_7217_, 3);
                lean_inc_ref(v_mctxAfter_7233_);
                if v_isShared_7232_ == 0 {
                    lean_ctor_set(v___x_7231_, 3, v_mctxAfter_7233_);
                    v___x_7235_ = v___x_7231_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7242_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 0, v_env_7223_);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 1, v_cmdEnv_x3f_7224_);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 2, v_fileMap_7225_);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 3, v_mctxAfter_7233_);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 4, v_options_7226_);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 5, v_currNamespace_7227_);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 6, v_openDecls_7228_);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 7, v_ngen_7229_);
                    v___x_7235_ = v_reuseFailAlloc_7242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7222_ == 0 {
                    lean_ctor_set(v___x_7221_, 0, v___x_7235_);
                    v___x_7237_ = v___x_7221_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7241_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7241_, 0, v___x_7235_);
                    lean_ctor_set(v_reuseFailAlloc_7241_, 1, v_parentDecl_x3f_7218_);
                    lean_ctor_set(v_reuseFailAlloc_7241_, 2, v_autoImplicits_7219_);
                    v___x_7237_ = v_reuseFailAlloc_7241_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_7215_ == 0 {
                    lean_ctor_set(v___x_7214_, 0, v___x_7237_);
                    v___x_7239_ = v___x_7214_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7240_, 0, v___x_7237_);
                    v___x_7239_ = v_reuseFailAlloc_7240_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_updateContext_x3f___boxed(
    mut v_x_7248_: *mut LeanObject,
    mut v_x_7249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7250_: *mut LeanObject = core::ptr::null_mut();
    v_res_7250_ = l_Lean_Elab_Info_updateContext_x3f(v_x_7248_, v_x_7249_);
    lean_dec_ref(v_x_7249_);
    return v_res_7250_;
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(
    mut v_x_7251_: *mut LeanObject,
    mut v_x_7252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7252_) == 0 {
                    return v_x_7251_;
                } else {
                    v_head_7253_ = lean_ctor_get(v_x_7252_, 0);
                    v_tail_7254_ = lean_ctor_get(v_x_7252_, 1);
                    v___x_7255_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2;
                    v___x_7256_ = lean_string_append(v_x_7251_, v___x_7255_);
                    v___x_7257_ = lean_expr_dbg_to_string(v_head_7253_);
                    v___x_7258_ = lean_string_append(v___x_7256_, v___x_7257_);
                    lean_dec_ref(v___x_7257_);
                    v_x_7251_ = v___x_7258_;
                    v_x_7252_ = v_tail_7254_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(
    mut v_x_7260_: *mut LeanObject,
    mut v_x_7261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7262_: *mut LeanObject = core::ptr::null_mut();
    v_res_7262_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_7260_, v_x_7261_);
    lean_dec(v_x_7261_);
    return v_res_7262_;
}
pub unsafe fn l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(
    mut v_x_7265_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_7265_) == 0 {
        let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
        v___x_7266_ =
            l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0;
        return v___x_7266_;
    } else {
        let mut v_tail_7267_: *mut LeanObject = core::ptr::null_mut();
        v_tail_7267_ = lean_ctor_get(v_x_7265_, 1);
        if lean_obj_tag(v_tail_7267_) == 0 {
            let mut v_head_7268_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7269_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7270_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
            v_head_7268_ = lean_ctor_get(v_x_7265_, 0);
            v___x_7269_ =
                l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1;
            v___x_7270_ = lean_expr_dbg_to_string(v_head_7268_);
            v___x_7271_ = lean_string_append(v___x_7269_, v___x_7270_);
            lean_dec_ref(v___x_7270_);
            v___x_7272_ = l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1;
            v___x_7273_ = lean_string_append(v___x_7271_, v___x_7272_);
            return v___x_7273_;
        } else {
            let mut v_head_7274_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7279_: u32 = 0;
            let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
            v_head_7274_ = lean_ctor_get(v_x_7265_, 0);
            v___x_7275_ =
                l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1;
            v___x_7276_ = lean_expr_dbg_to_string(v_head_7274_);
            v___x_7277_ = lean_string_append(v___x_7275_, v___x_7276_);
            lean_dec_ref(v___x_7276_);
            v___x_7278_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_7277_, v_tail_7267_);
            v___x_7279_ = 93;
            v___x_7280_ = lean_string_push(v___x_7278_, v___x_7279_);
            return v___x_7280_;
        }
    }
}
pub unsafe fn l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(
    mut v_x_7281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7282_: *mut LeanObject = core::ptr::null_mut();
    v_res_7282_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_7281_);
    lean_dec(v_x_7281_);
    return v_res_7282_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_format(
    mut v_ctx_7289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parentDecl_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7294_: u8 = 0;
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: u8 = 0;
    let mut v___x_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7304_: u8 = 0;
    let mut v_autoImplicits_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7308_: u8 = 0;
    let mut v___x_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_ctx_7289_) {
                0 => {
                    lean_dec_ref_known(v_ctx_7289_, 1);
                    v___x_7290_ = l_Lean_Elab_PartialContextInfo_format___closed__1;
                    return v___x_7290_;
                }
                1 => {
                    v_parentDecl_7291_ = lean_ctor_get(v_ctx_7289_, 0);
                    v_isSharedCheck_7304_ = (!lean_is_exclusive(v_ctx_7289_)) as u8;
                    if v_isSharedCheck_7304_ == 0 {
                        v___x_7293_ = v_ctx_7289_;
                        v_isShared_7294_ = v_isSharedCheck_7304_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_parentDecl_7291_);
                        lean_dec(v_ctx_7289_);
                        v___x_7293_ = lean_box(0);
                        v_isShared_7294_ = v_isSharedCheck_7304_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_autoImplicits_7305_ = lean_ctor_get(v_ctx_7289_, 0);
                    v_isSharedCheck_7320_ = (!lean_is_exclusive(v_ctx_7289_)) as u8;
                    if v_isSharedCheck_7320_ == 0 {
                        v___x_7307_ = v_ctx_7289_;
                        v_isShared_7308_ = v_isSharedCheck_7320_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_autoImplicits_7305_);
                        lean_dec(v_ctx_7289_);
                        v___x_7307_ = lean_box(0);
                        v_isShared_7308_ = v_isSharedCheck_7320_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_7295_ = l_Lean_Elab_PartialContextInfo_format___closed__2;
                v___x_7296_ = 1;
                v___x_7297_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_parentDecl_7291_,
                    v___x_7296_,
                );
                v___x_7298_ = lean_string_append(v___x_7295_, v___x_7297_);
                lean_dec_ref(v___x_7297_);
                v___x_7299_ = l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1;
                v___x_7300_ = lean_string_append(v___x_7298_, v___x_7299_);
                if v_isShared_7294_ == 0 {
                    lean_ctor_set_tag(v___x_7293_, 3);
                    lean_ctor_set(v___x_7293_, 0, v___x_7300_);
                    v___x_7302_ = v___x_7293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7303_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7303_, 0, v___x_7300_);
                    v___x_7302_ = v_reuseFailAlloc_7303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7302_;
            }
            3 => {
                v___x_7309_ = l_Lean_Elab_PartialContextInfo_format___closed__3;
                v___x_7310_ = l_Lean_Elab_PartialContextInfo_format___closed__4;
                v___x_7311_ = lean_array_to_list(v_autoImplicits_7305_);
                v___x_7312_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(
                    v___x_7311_,
                );
                lean_dec(v___x_7311_);
                v___x_7313_ = lean_string_append(v___x_7310_, v___x_7312_);
                lean_dec_ref(v___x_7312_);
                v___x_7314_ = lean_string_append(v___x_7309_, v___x_7313_);
                lean_dec_ref(v___x_7313_);
                v___x_7315_ = l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1;
                v___x_7316_ = lean_string_append(v___x_7314_, v___x_7315_);
                if v_isShared_7308_ == 0 {
                    lean_ctor_set_tag(v___x_7307_, 3);
                    lean_ctor_set(v___x_7307_, 0, v___x_7316_);
                    v___x_7318_ = v___x_7307_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7319_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7319_, 0, v___x_7316_);
                    v___x_7318_ = v_reuseFailAlloc_7319_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_format(
    mut v_tree_7330_: *mut LeanObject,
    mut v_ctx_x3f_7331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7343_: u8 = 0;
    let mut v_val_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7349_: u8 = 0;
    let mut v_size_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: u8 = 0;
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7360_: u8 = 0;
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7372_: u8 = 0;
    let mut v_a_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7376_: u8 = 0;
    let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7380_: u8 = 0;
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7389_: u8 = 0;
    let mut v_isSharedCheck_7390_: u8 = 0;
    let mut v_mvarId_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7394_: u8 = 0;
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: u8 = 0;
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_tree_7330_) {
                0 => {
                    v_i_7333_ = lean_ctor_get(v_tree_7330_, 0);
                    lean_inc_ref(v_i_7333_);
                    v_t_7334_ = lean_ctor_get(v_tree_7330_, 1);
                    lean_inc_ref(v_t_7334_);
                    lean_dec_ref_known(v_tree_7330_, 2);
                    v___x_7335_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
                        v_i_7333_,
                        v_ctx_x3f_7331_,
                    );
                    v_tree_7330_ = v_t_7334_;
                    v_ctx_x3f_7331_ = v___x_7335_;
                    state = 0;
                    continue;
                }
                1 => {
                    if lean_obj_tag(v_ctx_x3f_7331_) == 0 {
                        lean_dec_ref_known(v_tree_7330_, 2);
                        v___x_7337_ = l_Lean_Elab_InfoTree_format___closed__1;
                        v___x_7338_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7338_, 0, v___x_7337_);
                        return v___x_7338_;
                    } else {
                        v_i_7339_ = lean_ctor_get(v_tree_7330_, 0);
                        v_children_7340_ = lean_ctor_get(v_tree_7330_, 1);
                        v_isSharedCheck_7390_ = (!lean_is_exclusive(v_tree_7330_)) as u8;
                        if v_isSharedCheck_7390_ == 0 {
                            v___x_7342_ = v_tree_7330_;
                            v_isShared_7343_ = v_isSharedCheck_7390_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_children_7340_);
                            lean_inc(v_i_7339_);
                            lean_dec(v_tree_7330_);
                            v___x_7342_ = lean_box(0);
                            v_isShared_7343_ = v_isSharedCheck_7390_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    lean_dec(v_ctx_x3f_7331_);
                    v_mvarId_7391_ = lean_ctor_get(v_tree_7330_, 0);
                    v_isSharedCheck_7404_ = (!lean_is_exclusive(v_tree_7330_)) as u8;
                    if v_isSharedCheck_7404_ == 0 {
                        v___x_7393_ = v_tree_7330_;
                        v_isShared_7394_ = v_isSharedCheck_7404_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_mvarId_7391_);
                        lean_dec(v_tree_7330_);
                        v___x_7393_ = lean_box(0);
                        v_isShared_7394_ = v_isSharedCheck_7404_;
                        state = 10;
                        continue;
                    }
                }
            },
            1 => {
                v_val_7344_ = lean_ctor_get(v_ctx_x3f_7331_, 0);
                lean_inc_ref(v_i_7339_);
                lean_inc(v_val_7344_);
                v___x_7345_ = l_Lean_Elab_Info_format(v_val_7344_, v_i_7339_);
                if lean_obj_tag(v___x_7345_) == 0 {
                    v_a_7346_ = lean_ctor_get(v___x_7345_, 0);
                    v_isSharedCheck_7389_ = (!lean_is_exclusive(v___x_7345_)) as u8;
                    if v_isSharedCheck_7389_ == 0 {
                        v___x_7348_ = v___x_7345_;
                        v_isShared_7349_ = v_isSharedCheck_7389_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7346_);
                        lean_dec(v___x_7345_);
                        v___x_7348_ = lean_box(0);
                        v_isShared_7349_ = v_isSharedCheck_7389_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7342_);
                    lean_dec_ref(v_children_7340_);
                    lean_dec_ref_known(v_ctx_x3f_7331_, 1);
                    lean_dec_ref(v_i_7339_);
                    return v___x_7345_;
                }
            }
            2 => {
                v_size_7350_ = lean_ctor_get(v_children_7340_, 2);
                v___x_7351_ = lean_unsigned_to_nat(0);
                v___x_7352_ = lean_nat_dec_eq(v_size_7350_, v___x_7351_);
                if v___x_7352_ == 0 {
                    lean_del_object(v___x_7348_);
                    v___x_7353_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_7331_, v_i_7339_);
                    lean_dec_ref(v_i_7339_);
                    v___x_7354_ = l_Lean_PersistentArray_toList___redArg(v_children_7340_);
                    lean_dec_ref(v_children_7340_);
                    v___x_7355_ = lean_box(0);
                    v___x_7356_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(
                        v___x_7353_,
                        v___x_7354_,
                        v___x_7355_,
                    );
                    if lean_obj_tag(v___x_7356_) == 0 {
                        v_a_7357_ = lean_ctor_get(v___x_7356_, 0);
                        v_isSharedCheck_7372_ = (!lean_is_exclusive(v___x_7356_)) as u8;
                        if v_isSharedCheck_7372_ == 0 {
                            v___x_7359_ = v___x_7356_;
                            v_isShared_7360_ = v_isSharedCheck_7372_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7357_);
                            lean_dec(v___x_7356_);
                            v___x_7359_ = lean_box(0);
                            v_isShared_7360_ = v_isSharedCheck_7372_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_7346_);
                        lean_del_object(v___x_7342_);
                        v_a_7373_ = lean_ctor_get(v___x_7356_, 0);
                        v_isSharedCheck_7380_ = (!lean_is_exclusive(v___x_7356_)) as u8;
                        if v_isSharedCheck_7380_ == 0 {
                            v___x_7375_ = v___x_7356_;
                            v_isShared_7376_ = v_isSharedCheck_7380_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7373_);
                            lean_dec(v___x_7356_);
                            v___x_7375_ = lean_box(0);
                            v_isShared_7376_ = v_isSharedCheck_7380_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_children_7340_);
                    lean_dec_ref(v_i_7339_);
                    lean_dec_ref_known(v_ctx_x3f_7331_, 1);
                    v___x_7381_ = l_Lean_Elab_InfoTree_format___closed__3;
                    if v_isShared_7343_ == 0 {
                        lean_ctor_set_tag(v___x_7342_, 5);
                        lean_ctor_set(v___x_7342_, 1, v_a_7346_);
                        lean_ctor_set(v___x_7342_, 0, v___x_7381_);
                        v___x_7383_ = v___x_7342_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7388_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7388_, 0, v___x_7381_);
                        lean_ctor_set(v_reuseFailAlloc_7388_, 1, v_a_7346_);
                        v___x_7383_ = v_reuseFailAlloc_7388_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7361_ = l_Lean_Elab_InfoTree_format___closed__3;
                if v_isShared_7343_ == 0 {
                    lean_ctor_set_tag(v___x_7342_, 5);
                    lean_ctor_set(v___x_7342_, 1, v_a_7346_);
                    lean_ctor_set(v___x_7342_, 0, v___x_7361_);
                    v___x_7363_ = v___x_7342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7371_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7371_, 0, v___x_7361_);
                    lean_ctor_set(v_reuseFailAlloc_7371_, 1, v_a_7346_);
                    v___x_7363_ = v_reuseFailAlloc_7371_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7364_ = lean_box(1);
                v___x_7365_ =
                    l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(
                        v___x_7364_,
                        v_a_7357_,
                    );
                v___x_7366_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_7366_, 0, v___x_7363_);
                lean_ctor_set(v___x_7366_, 1, v___x_7365_);
                v___x_7367_ = l_Std_Format_nestD(v___x_7366_);
                if v_isShared_7360_ == 0 {
                    lean_ctor_set(v___x_7359_, 0, v___x_7367_);
                    v___x_7369_ = v___x_7359_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7370_, 0, v___x_7367_);
                    v___x_7369_ = v_reuseFailAlloc_7370_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7369_;
            }
            6 => {
                if v_isShared_7376_ == 0 {
                    v___x_7378_ = v___x_7375_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7379_, 0, v_a_7373_);
                    v___x_7378_ = v_reuseFailAlloc_7379_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7378_;
            }
            8 => {
                v___x_7384_ = l_Std_Format_nestD(v___x_7383_);
                if v_isShared_7349_ == 0 {
                    lean_ctor_set(v___x_7348_, 0, v___x_7384_);
                    v___x_7386_ = v___x_7348_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7387_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7387_, 0, v___x_7384_);
                    v___x_7386_ = v_reuseFailAlloc_7387_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7386_;
            }
            10 => {
                v___x_7395_ = l_Lean_Elab_InfoTree_format___closed__5;
                v___x_7396_ = 1;
                v___x_7397_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_mvarId_7391_,
                    v___x_7396_,
                );
                if v_isShared_7394_ == 0 {
                    lean_ctor_set_tag(v___x_7393_, 3);
                    lean_ctor_set(v___x_7393_, 0, v___x_7397_);
                    v___x_7399_ = v___x_7393_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7403_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7403_, 0, v___x_7397_);
                    v___x_7399_ = v_reuseFailAlloc_7403_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_7400_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_7400_, 0, v___x_7395_);
                lean_ctor_set(v___x_7400_, 1, v___x_7399_);
                v___x_7401_ = l_Std_Format_nestD(v___x_7400_);
                v___x_7402_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7402_, 0, v___x_7401_);
                return v___x_7402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(
    mut v___x_7405_: *mut LeanObject,
    mut v_x_7406_: *mut LeanObject,
    mut v_x_7407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7415_: u8 = 0;
    let mut v___x_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7425_: u8 = 0;
    let mut v___x_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7429_: u8 = 0;
    let mut v_isSharedCheck_7430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7406_) == 0 {
                    lean_dec(v___x_7405_);
                    v___x_7409_ = l_List_reverse___redArg(v_x_7407_);
                    v___x_7410_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7410_, 0, v___x_7409_);
                    return v___x_7410_;
                } else {
                    v_head_7411_ = lean_ctor_get(v_x_7406_, 0);
                    v_tail_7412_ = lean_ctor_get(v_x_7406_, 1);
                    v_isSharedCheck_7430_ = (!lean_is_exclusive(v_x_7406_)) as u8;
                    if v_isSharedCheck_7430_ == 0 {
                        v___x_7414_ = v_x_7406_;
                        v_isShared_7415_ = v_isSharedCheck_7430_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7412_);
                        lean_inc(v_head_7411_);
                        lean_dec(v_x_7406_);
                        v___x_7414_ = lean_box(0);
                        v_isShared_7415_ = v_isSharedCheck_7430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_7405_);
                v___x_7416_ = l_Lean_Elab_InfoTree_format(v_head_7411_, v___x_7405_);
                if lean_obj_tag(v___x_7416_) == 0 {
                    v_a_7417_ = lean_ctor_get(v___x_7416_, 0);
                    lean_inc(v_a_7417_);
                    lean_dec_ref_known(v___x_7416_, 1);
                    if v_isShared_7415_ == 0 {
                        lean_ctor_set(v___x_7414_, 1, v_x_7407_);
                        lean_ctor_set(v___x_7414_, 0, v_a_7417_);
                        v___x_7419_ = v___x_7414_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7421_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7421_, 0, v_a_7417_);
                        lean_ctor_set(v_reuseFailAlloc_7421_, 1, v_x_7407_);
                        v___x_7419_ = v_reuseFailAlloc_7421_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7414_);
                    lean_dec(v_tail_7412_);
                    lean_dec(v_x_7407_);
                    lean_dec(v___x_7405_);
                    v_a_7422_ = lean_ctor_get(v___x_7416_, 0);
                    v_isSharedCheck_7429_ = (!lean_is_exclusive(v___x_7416_)) as u8;
                    if v_isSharedCheck_7429_ == 0 {
                        v___x_7424_ = v___x_7416_;
                        v_isShared_7425_ = v_isSharedCheck_7429_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7422_);
                        lean_dec(v___x_7416_);
                        v___x_7424_ = lean_box(0);
                        v_isShared_7425_ = v_isSharedCheck_7429_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_7406_ = v_tail_7412_;
                v_x_7407_ = v___x_7419_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_7425_ == 0 {
                    v___x_7427_ = v___x_7424_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7428_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7428_, 0, v_a_7422_);
                    v___x_7427_ = v_reuseFailAlloc_7428_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(
    mut v___x_7431_: *mut LeanObject,
    mut v_x_7432_: *mut LeanObject,
    mut v_x_7433_: *mut LeanObject,
    mut v___y_7434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7435_: *mut LeanObject = core::ptr::null_mut();
    v_res_7435_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(
        v___x_7431_,
        v_x_7432_,
        v_x_7433_,
    );
    return v_res_7435_;
}
pub unsafe fn l_Lean_Elab_InfoTree_format___boxed(
    mut v_tree_7436_: *mut LeanObject,
    mut v_ctx_x3f_7437_: *mut LeanObject,
    mut v_a_7438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7439_: *mut LeanObject = core::ptr::null_mut();
    v_res_7439_ = l_Lean_Elab_InfoTree_format(v_tree_7436_, v_ctx_x3f_7437_);
    return v_res_7439_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(
    mut v_f_7440_: *mut LeanObject,
    mut v_s_7441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_7442_: u8 = 0;
    let mut v_assignment_7443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7448_: u8 = 0;
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_enabled_7442_ = lean_ctor_get_uint8(
                    v_s_7441_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_7443_ = lean_ctor_get(v_s_7441_, 0);
                v_lazyAssignment_7444_ = lean_ctor_get(v_s_7441_, 1);
                v_trees_7445_ = lean_ctor_get(v_s_7441_, 2);
                v_isSharedCheck_7453_ = (!lean_is_exclusive(v_s_7441_)) as u8;
                if v_isSharedCheck_7453_ == 0 {
                    v___x_7447_ = v_s_7441_;
                    v_isShared_7448_ = v_isSharedCheck_7453_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_trees_7445_);
                    lean_inc(v_lazyAssignment_7444_);
                    lean_inc(v_assignment_7443_);
                    lean_dec(v_s_7441_);
                    v___x_7447_ = lean_box(0);
                    v_isShared_7448_ = v_isSharedCheck_7453_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7449_ = lean_apply_1(v_f_7440_, v_trees_7445_);
                if v_isShared_7448_ == 0 {
                    lean_ctor_set(v___x_7447_, 2, v___x_7449_);
                    v___x_7451_ = v___x_7447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7452_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7452_, 0, v_assignment_7443_);
                    lean_ctor_set(v_reuseFailAlloc_7452_, 1, v_lazyAssignment_7444_);
                    lean_ctor_set(v_reuseFailAlloc_7452_, 2, v___x_7449_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7452_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_7442_,
                    );
                    v___x_7451_ = v_reuseFailAlloc_7452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(
    mut v_inst_7454_: *mut LeanObject,
    mut v_f_7455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyInfoState_7456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7458_: *mut LeanObject = core::ptr::null_mut();
    v_modifyInfoState_7456_ = lean_ctor_get(v_inst_7454_, 1);
    lean_inc(v_modifyInfoState_7456_);
    lean_dec_ref(v_inst_7454_);
    v___f_7457_ = lean_alloc_closure(
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7457_, 0, v_f_7455_);
    v___x_7458_ = lean_apply_1(v_modifyInfoState_7456_, v___f_7457_);
    return v___x_7458_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(
    mut v_m_7459_: *mut LeanObject,
    mut v_inst_7460_: *mut LeanObject,
    mut v_f_7461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyInfoState_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
    v_modifyInfoState_7462_ = lean_ctor_get(v_inst_7460_, 1);
    lean_inc(v_modifyInfoState_7462_);
    lean_dec_ref(v_inst_7460_);
    v___f_7463_ = lean_alloc_closure(
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7463_, 0, v_f_7461_);
    v___x_7464_ = lean_apply_1(v_modifyInfoState_7462_, v___f_7463_);
    return v___x_7464_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0() -> *mut LeanObject
{
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut LeanObject = core::ptr::null_mut();
    v___x_7465_ = lean_unsigned_to_nat(32);
    v___x_7466_ = lean_mk_empty_array_with_capacity(v___x_7465_);
    v___x_7467_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7467_, 0, v___x_7466_);
    return v___x_7467_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1() -> *mut LeanObject
{
    let mut v___x_7468_: usize = 0;
    let mut v___x_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7473_: *mut LeanObject = core::ptr::null_mut();
    v___x_7468_ = 5usize;
    v___x_7469_ = lean_unsigned_to_nat(0);
    v___x_7470_ = lean_unsigned_to_nat(32);
    v___x_7471_ = lean_mk_empty_array_with_capacity(v___x_7470_);
    v___x_7472_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once),
        _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0,
    );
    v___x_7473_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_7473_, 0, v___x_7472_);
    lean_ctor_set(v___x_7473_, 1, v___x_7471_);
    lean_ctor_set(v___x_7473_, 2, v___x_7469_);
    lean_ctor_set(v___x_7473_, 3, v___x_7469_);
    lean_ctor_set_usize(v___x_7473_, 4, v___x_7468_);
    return v___x_7473_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___redArg___lam__0(
    mut v_s_7474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_7475_: u8 = 0;
    let mut v_assignment_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_7477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7480_: u8 = 0;
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7485_: u8 = 0;
    let mut v_unused_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_enabled_7475_ = lean_ctor_get_uint8(
                    v_s_7474_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_7476_ = lean_ctor_get(v_s_7474_, 0);
                v_lazyAssignment_7477_ = lean_ctor_get(v_s_7474_, 1);
                v_isSharedCheck_7485_ = (!lean_is_exclusive(v_s_7474_)) as u8;
                if v_isSharedCheck_7485_ == 0 {
                    v_unused_7486_ = lean_ctor_get(v_s_7474_, 2);
                    lean_dec(v_unused_7486_);
                    v___x_7479_ = v_s_7474_;
                    v_isShared_7480_ = v_isSharedCheck_7485_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_7477_);
                    lean_inc(v_assignment_7476_);
                    lean_dec(v_s_7474_);
                    v___x_7479_ = lean_box(0);
                    v_isShared_7480_ = v_isSharedCheck_7485_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7481_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1,
                );
                if v_isShared_7480_ == 0 {
                    lean_ctor_set(v___x_7479_, 2, v___x_7481_);
                    v___x_7483_ = v___x_7479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7484_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7484_, 0, v_assignment_7476_);
                    lean_ctor_set(v_reuseFailAlloc_7484_, 1, v_lazyAssignment_7477_);
                    lean_ctor_set(v_reuseFailAlloc_7484_, 2, v___x_7481_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7484_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_7475_,
                    );
                    v___x_7483_ = v_reuseFailAlloc_7484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___redArg___lam__1(
    mut v_toPure_7487_: *mut LeanObject,
    mut v_trees_7488_: *mut LeanObject,
    mut v_____r_7489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7490_: *mut LeanObject = core::ptr::null_mut();
    v___x_7490_ = lean_apply_2(v_toPure_7487_, lean_box(0), v_trees_7488_);
    return v___x_7490_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___redArg___lam__2(
    mut v_toPure_7491_: *mut LeanObject,
    mut v_modifyInfoState_7492_: *mut LeanObject,
    mut v___f_7493_: *mut LeanObject,
    mut v_toBind_7494_: *mut LeanObject,
    mut v_____do__lift_7495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_trees_7496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: *mut LeanObject = core::ptr::null_mut();
    v_trees_7496_ = lean_ctor_get(v_____do__lift_7495_, 2);
    lean_inc_ref(v_trees_7496_);
    lean_dec_ref(v_____do__lift_7495_);
    v___f_7497_ = lean_alloc_closure(
        l_Lean_Elab_getResetInfoTrees___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7497_, 0, v_toPure_7491_);
    lean_closure_set(v___f_7497_, 1, v_trees_7496_);
    v___x_7498_ = lean_apply_1(v_modifyInfoState_7492_, v___f_7493_);
    v___x_7499_ = lean_apply_4(
        v_toBind_7494_,
        lean_box(0),
        lean_box(0),
        v___x_7498_,
        v___f_7497_,
    );
    return v___x_7499_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___redArg(
    mut v_inst_7501_: *mut LeanObject,
    mut v_inst_7502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7503_ = lean_ctor_get(v_inst_7501_, 0);
    lean_inc_ref(v_toApplicative_7503_);
    v_toBind_7504_ = lean_ctor_get(v_inst_7501_, 1);
    lean_inc_n(v_toBind_7504_, 2);
    lean_dec_ref(v_inst_7501_);
    v_getInfoState_7505_ = lean_ctor_get(v_inst_7502_, 0);
    lean_inc(v_getInfoState_7505_);
    v_modifyInfoState_7506_ = lean_ctor_get(v_inst_7502_, 1);
    lean_inc(v_modifyInfoState_7506_);
    lean_dec_ref(v_inst_7502_);
    v_toPure_7507_ = lean_ctor_get(v_toApplicative_7503_, 1);
    lean_inc(v_toPure_7507_);
    lean_dec_ref(v_toApplicative_7503_);
    v___f_7508_ = l_Lean_Elab_getResetInfoTrees___redArg___closed__0;
    v___f_7509_ = lean_alloc_closure(
        l_Lean_Elab_getResetInfoTrees___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7509_, 0, v_toPure_7507_);
    lean_closure_set(v___f_7509_, 1, v_modifyInfoState_7506_);
    lean_closure_set(v___f_7509_, 2, v___f_7508_);
    lean_closure_set(v___f_7509_, 3, v_toBind_7504_);
    v___x_7510_ = lean_apply_4(
        v_toBind_7504_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_7505_,
        v___f_7509_,
    );
    return v___x_7510_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees(
    mut v_m_7511_: *mut LeanObject,
    mut v_inst_7512_: *mut LeanObject,
    mut v_inst_7513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    v___x_7514_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_7512_, v_inst_7513_);
    return v___x_7514_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___redArg___lam__0(
    mut v_t_7515_: *mut LeanObject,
    mut v_s_7516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_7517_: u8 = 0;
    let mut v_assignment_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7523_: u8 = 0;
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_enabled_7517_ = lean_ctor_get_uint8(
                    v_s_7516_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_7518_ = lean_ctor_get(v_s_7516_, 0);
                v_lazyAssignment_7519_ = lean_ctor_get(v_s_7516_, 1);
                v_trees_7520_ = lean_ctor_get(v_s_7516_, 2);
                v_isSharedCheck_7528_ = (!lean_is_exclusive(v_s_7516_)) as u8;
                if v_isSharedCheck_7528_ == 0 {
                    v___x_7522_ = v_s_7516_;
                    v_isShared_7523_ = v_isSharedCheck_7528_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_trees_7520_);
                    lean_inc(v_lazyAssignment_7519_);
                    lean_inc(v_assignment_7518_);
                    lean_dec(v_s_7516_);
                    v___x_7522_ = lean_box(0);
                    v_isShared_7523_ = v_isSharedCheck_7528_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7524_ = l_Lean_PersistentArray_push___redArg(v_trees_7520_, v_t_7515_);
                if v_isShared_7523_ == 0 {
                    lean_ctor_set(v___x_7522_, 2, v___x_7524_);
                    v___x_7526_ = v___x_7522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7527_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 0, v_assignment_7518_);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 1, v_lazyAssignment_7519_);
                    lean_ctor_set(v_reuseFailAlloc_7527_, 2, v___x_7524_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7527_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_7517_,
                    );
                    v___x_7526_ = v_reuseFailAlloc_7527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___redArg___lam__1(
    mut v_toApplicative_7529_: *mut LeanObject,
    mut v_modifyInfoState_7530_: *mut LeanObject,
    mut v___f_7531_: *mut LeanObject,
    mut v_____do__lift_7532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_7533_: u8 = 0;
    v_enabled_7533_ = lean_ctor_get_uint8(
        v_____do__lift_7532_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    if v_enabled_7533_ == 0 {
        let mut v_toPure_7534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_7531_);
        lean_dec(v_modifyInfoState_7530_);
        v_toPure_7534_ = lean_ctor_get(v_toApplicative_7529_, 1);
        lean_inc(v_toPure_7534_);
        lean_dec_ref(v_toApplicative_7529_);
        v___x_7535_ = lean_box(0);
        v___x_7536_ = lean_apply_2(v_toPure_7534_, lean_box(0), v___x_7535_);
        return v___x_7536_;
    } else {
        let mut v___x_7537_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_7529_);
        v___x_7537_ = lean_apply_1(v_modifyInfoState_7530_, v___f_7531_);
        return v___x_7537_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(
    mut v_toApplicative_7538_: *mut LeanObject,
    mut v_modifyInfoState_7539_: *mut LeanObject,
    mut v___f_7540_: *mut LeanObject,
    mut v_____do__lift_7541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7542_: *mut LeanObject = core::ptr::null_mut();
    v_res_7542_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(
        v_toApplicative_7538_,
        v_modifyInfoState_7539_,
        v___f_7540_,
        v_____do__lift_7541_,
    );
    lean_dec_ref(v_____do__lift_7541_);
    return v_res_7542_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___redArg(
    mut v_inst_7543_: *mut LeanObject,
    mut v_inst_7544_: *mut LeanObject,
    mut v_t_7545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_7548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7552_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7546_ = lean_ctor_get(v_inst_7543_, 0);
    lean_inc_ref(v_toApplicative_7546_);
    v_toBind_7547_ = lean_ctor_get(v_inst_7543_, 1);
    lean_inc(v_toBind_7547_);
    lean_dec_ref(v_inst_7543_);
    v_getInfoState_7548_ = lean_ctor_get(v_inst_7544_, 0);
    lean_inc(v_getInfoState_7548_);
    v_modifyInfoState_7549_ = lean_ctor_get(v_inst_7544_, 1);
    lean_inc(v_modifyInfoState_7549_);
    lean_dec_ref(v_inst_7544_);
    v___f_7550_ = lean_alloc_closure(
        l_Lean_Elab_pushInfoTree___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7550_, 0, v_t_7545_);
    v___f_7551_ = lean_alloc_closure(
        l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7551_, 0, v_toApplicative_7546_);
    lean_closure_set(v___f_7551_, 1, v_modifyInfoState_7549_);
    lean_closure_set(v___f_7551_, 2, v___f_7550_);
    v___x_7552_ = lean_apply_4(
        v_toBind_7547_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_7548_,
        v___f_7551_,
    );
    return v___x_7552_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree(
    mut v_m_7553_: *mut LeanObject,
    mut v_inst_7554_: *mut LeanObject,
    mut v_inst_7555_: *mut LeanObject,
    mut v_t_7556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7557_: *mut LeanObject = core::ptr::null_mut();
    v___x_7557_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_7554_, v_inst_7555_, v_t_7556_);
    return v___x_7557_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___redArg___lam__0(
    mut v_toApplicative_7558_: *mut LeanObject,
    mut v_t_7559_: *mut LeanObject,
    mut v_inst_7560_: *mut LeanObject,
    mut v_inst_7561_: *mut LeanObject,
    mut v_____do__lift_7562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_7563_: u8 = 0;
    v_enabled_7563_ = lean_ctor_get_uint8(
        v_____do__lift_7562_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    if v_enabled_7563_ == 0 {
        let mut v_toPure_7564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7566_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_7561_);
        lean_dec_ref(v_inst_7560_);
        lean_dec_ref(v_t_7559_);
        v_toPure_7564_ = lean_ctor_get(v_toApplicative_7558_, 1);
        lean_inc(v_toPure_7564_);
        lean_dec_ref(v_toApplicative_7558_);
        v___x_7565_ = lean_box(0);
        v___x_7566_ = lean_apply_2(v_toPure_7564_, lean_box(0), v___x_7565_);
        return v___x_7566_;
    } else {
        let mut v___x_7567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_7558_);
        v___x_7567_ = lean_unsigned_to_nat(32);
        v___x_7568_ = lean_mk_empty_array_with_capacity(v___x_7567_);
        lean_dec_ref(v___x_7568_);
        v___x_7569_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1,
        );
        v___x_7570_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_7570_, 0, v_t_7559_);
        lean_ctor_set(v___x_7570_, 1, v___x_7569_);
        v___x_7571_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_7560_, v_inst_7561_, v___x_7570_);
        return v___x_7571_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(
    mut v_toApplicative_7572_: *mut LeanObject,
    mut v_t_7573_: *mut LeanObject,
    mut v_inst_7574_: *mut LeanObject,
    mut v_inst_7575_: *mut LeanObject,
    mut v_____do__lift_7576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7577_: *mut LeanObject = core::ptr::null_mut();
    v_res_7577_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(
        v_toApplicative_7572_,
        v_t_7573_,
        v_inst_7574_,
        v_inst_7575_,
        v_____do__lift_7576_,
    );
    lean_dec_ref(v_____do__lift_7576_);
    return v_res_7577_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___redArg(
    mut v_inst_7578_: *mut LeanObject,
    mut v_inst_7579_: *mut LeanObject,
    mut v_t_7580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7581_ = lean_ctor_get(v_inst_7578_, 0);
    lean_inc_ref(v_toApplicative_7581_);
    v_toBind_7582_ = lean_ctor_get(v_inst_7578_, 1);
    lean_inc(v_toBind_7582_);
    v_getInfoState_7583_ = lean_ctor_get(v_inst_7579_, 0);
    lean_inc(v_getInfoState_7583_);
    v___f_7584_ = lean_alloc_closure(
        l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7584_, 0, v_toApplicative_7581_);
    lean_closure_set(v___f_7584_, 1, v_t_7580_);
    lean_closure_set(v___f_7584_, 2, v_inst_7578_);
    lean_closure_set(v___f_7584_, 3, v_inst_7579_);
    v___x_7585_ = lean_apply_4(
        v_toBind_7582_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_7583_,
        v___f_7584_,
    );
    return v___x_7585_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf(
    mut v_m_7586_: *mut LeanObject,
    mut v_inst_7587_: *mut LeanObject,
    mut v_inst_7588_: *mut LeanObject,
    mut v_t_7589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7590_: *mut LeanObject = core::ptr::null_mut();
    v___x_7590_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_7587_, v_inst_7588_, v_t_7589_);
    return v___x_7590_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___redArg(
    mut v_inst_7591_: *mut LeanObject,
    mut v_inst_7592_: *mut LeanObject,
    mut v_info_7593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut LeanObject = core::ptr::null_mut();
    v___x_7594_ = lean_alloc_ctor(8, 1, (0) as u32);
    lean_ctor_set(v___x_7594_, 0, v_info_7593_);
    v___x_7595_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_7591_, v_inst_7592_, v___x_7594_);
    return v___x_7595_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo(
    mut v_m_7596_: *mut LeanObject,
    mut v_inst_7597_: *mut LeanObject,
    mut v_inst_7598_: *mut LeanObject,
    mut v_info_7599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    v___x_7600_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_7597_, v_inst_7598_, v_info_7599_);
    return v___x_7600_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___redArg___lam__0(
    mut v_stx_7601_: *mut LeanObject,
    mut v_expectedType_x3f_7602_: *mut LeanObject,
    mut v_inst_7603_: *mut LeanObject,
    mut v_inst_7604_: *mut LeanObject,
    mut v_____do__lift_7605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: u8 = 0;
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7612_: *mut LeanObject = core::ptr::null_mut();
    v___x_7606_ = lean_box(0);
    v___x_7607_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7607_, 0, v___x_7606_);
    lean_ctor_set(v___x_7607_, 1, v_stx_7601_);
    v___x_7608_ = l_Lean_LocalContext_empty;
    v___x_7609_ = 0;
    v___x_7610_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_7610_, 0, v___x_7607_);
    lean_ctor_set(v___x_7610_, 1, v___x_7608_);
    lean_ctor_set(v___x_7610_, 2, v_expectedType_x3f_7602_);
    lean_ctor_set(v___x_7610_, 3, v_____do__lift_7605_);
    lean_ctor_set_uint8(
        v___x_7610_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_7609_,
    );
    lean_ctor_set_uint8(
        v___x_7610_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_7609_,
    );
    v___x_7611_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7611_, 0, v___x_7610_);
    v___x_7612_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_7603_, v_inst_7604_, v___x_7611_);
    return v___x_7612_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___redArg(
    mut v_inst_7613_: *mut LeanObject,
    mut v_inst_7614_: *mut LeanObject,
    mut v_inst_7615_: *mut LeanObject,
    mut v_inst_7616_: *mut LeanObject,
    mut v_stx_7617_: *mut LeanObject,
    mut v_n_7618_: *mut LeanObject,
    mut v_expectedType_x3f_7619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7623_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_7620_ = lean_ctor_get(v_inst_7613_, 1);
    lean_inc(v_toBind_7620_);
    lean_inc_ref(v_inst_7613_);
    v___f_7621_ = lean_alloc_closure(
        l_Lean_Elab_addConstInfo___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7621_, 0, v_stx_7617_);
    lean_closure_set(v___f_7621_, 1, v_expectedType_x3f_7619_);
    lean_closure_set(v___f_7621_, 2, v_inst_7613_);
    lean_closure_set(v___f_7621_, 3, v_inst_7614_);
    v___x_7622_ =
        l_Lean_mkConstWithLevelParams___redArg(v_inst_7613_, v_inst_7615_, v_inst_7616_, v_n_7618_);
    v___x_7623_ = lean_apply_4(
        v_toBind_7620_,
        lean_box(0),
        lean_box(0),
        v___x_7622_,
        v___f_7621_,
    );
    return v___x_7623_;
}
pub unsafe fn l_Lean_Elab_addConstInfo(
    mut v_m_7624_: *mut LeanObject,
    mut v_inst_7625_: *mut LeanObject,
    mut v_inst_7626_: *mut LeanObject,
    mut v_inst_7627_: *mut LeanObject,
    mut v_inst_7628_: *mut LeanObject,
    mut v_stx_7629_: *mut LeanObject,
    mut v_n_7630_: *mut LeanObject,
    mut v_expectedType_x3f_7631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7632_: *mut LeanObject = core::ptr::null_mut();
    v___x_7632_ = l_Lean_Elab_addConstInfo___redArg(
        v_inst_7625_,
        v_inst_7626_,
        v_inst_7627_,
        v_inst_7628_,
        v_stx_7629_,
        v_n_7630_,
        v_expectedType_x3f_7631_,
    );
    return v___x_7632_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(
    mut v_t_7633_: *mut LeanObject,
    mut v___y_7634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_7638_: u8 = 0;
    let mut v___x_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7653_: u8 = 0;
    let mut v_enabled_7654_: u8 = 0;
    let mut v_assignment_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7660_: u8 = 0;
    let mut v___x_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7671_: u8 = 0;
    let mut v_isSharedCheck_7672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7636_ = lean_st_ref_get(v___y_7634_);
                v_infoState_7637_ = lean_ctor_get(v___x_7636_, 7);
                lean_inc_ref(v_infoState_7637_);
                lean_dec(v___x_7636_);
                v_enabled_7638_ = lean_ctor_get_uint8(
                    v_infoState_7637_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_7637_);
                if v_enabled_7638_ == 0 {
                    lean_dec_ref(v_t_7633_);
                    v___x_7639_ = lean_box(0);
                    v___x_7640_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7640_, 0, v___x_7639_);
                    return v___x_7640_;
                } else {
                    v___x_7641_ = lean_st_ref_take(v___y_7634_);
                    v_infoState_7642_ = lean_ctor_get(v___x_7641_, 7);
                    v_env_7643_ = lean_ctor_get(v___x_7641_, 0);
                    v_nextMacroScope_7644_ = lean_ctor_get(v___x_7641_, 1);
                    v_ngen_7645_ = lean_ctor_get(v___x_7641_, 2);
                    v_auxDeclNGen_7646_ = lean_ctor_get(v___x_7641_, 3);
                    v_traceState_7647_ = lean_ctor_get(v___x_7641_, 4);
                    v_cache_7648_ = lean_ctor_get(v___x_7641_, 5);
                    v_messages_7649_ = lean_ctor_get(v___x_7641_, 6);
                    v_snapshotTasks_7650_ = lean_ctor_get(v___x_7641_, 8);
                    v_isSharedCheck_7672_ = (!lean_is_exclusive(v___x_7641_)) as u8;
                    if v_isSharedCheck_7672_ == 0 {
                        v___x_7652_ = v___x_7641_;
                        v_isShared_7653_ = v_isSharedCheck_7672_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_7650_);
                        lean_inc(v_infoState_7642_);
                        lean_inc(v_messages_7649_);
                        lean_inc(v_cache_7648_);
                        lean_inc(v_traceState_7647_);
                        lean_inc(v_auxDeclNGen_7646_);
                        lean_inc(v_ngen_7645_);
                        lean_inc(v_nextMacroScope_7644_);
                        lean_inc(v_env_7643_);
                        lean_dec(v___x_7641_);
                        v___x_7652_ = lean_box(0);
                        v_isShared_7653_ = v_isSharedCheck_7672_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_7654_ = lean_ctor_get_uint8(
                    v_infoState_7642_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_7655_ = lean_ctor_get(v_infoState_7642_, 0);
                v_lazyAssignment_7656_ = lean_ctor_get(v_infoState_7642_, 1);
                v_trees_7657_ = lean_ctor_get(v_infoState_7642_, 2);
                v_isSharedCheck_7671_ = (!lean_is_exclusive(v_infoState_7642_)) as u8;
                if v_isSharedCheck_7671_ == 0 {
                    v___x_7659_ = v_infoState_7642_;
                    v_isShared_7660_ = v_isSharedCheck_7671_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_trees_7657_);
                    lean_inc(v_lazyAssignment_7656_);
                    lean_inc(v_assignment_7655_);
                    lean_dec(v_infoState_7642_);
                    v___x_7659_ = lean_box(0);
                    v_isShared_7660_ = v_isSharedCheck_7671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7661_ = l_Lean_PersistentArray_push___redArg(v_trees_7657_, v_t_7633_);
                if v_isShared_7660_ == 0 {
                    lean_ctor_set(v___x_7659_, 2, v___x_7661_);
                    v___x_7663_ = v___x_7659_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7670_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7670_, 0, v_assignment_7655_);
                    lean_ctor_set(v_reuseFailAlloc_7670_, 1, v_lazyAssignment_7656_);
                    lean_ctor_set(v_reuseFailAlloc_7670_, 2, v___x_7661_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7670_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_7654_,
                    );
                    v___x_7663_ = v_reuseFailAlloc_7670_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7653_ == 0 {
                    lean_ctor_set(v___x_7652_, 7, v___x_7663_);
                    v___x_7665_ = v___x_7652_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7669_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 0, v_env_7643_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 1, v_nextMacroScope_7644_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 2, v_ngen_7645_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 3, v_auxDeclNGen_7646_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 4, v_traceState_7647_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 5, v_cache_7648_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 6, v_messages_7649_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 7, v___x_7663_);
                    lean_ctor_set(v_reuseFailAlloc_7669_, 8, v_snapshotTasks_7650_);
                    v___x_7665_ = v_reuseFailAlloc_7669_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7666_ = lean_st_ref_set(v___y_7634_, v___x_7665_);
                v___x_7667_ = lean_box(0);
                v___x_7668_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7668_, 0, v___x_7667_);
                return v___x_7668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_t_7673_: *mut LeanObject,
    mut v___y_7674_: *mut LeanObject,
    mut v___y_7675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7676_: *mut LeanObject = core::ptr::null_mut();
    v_res_7676_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_7673_, v___y_7674_);
    lean_dec(v___y_7674_);
    return v_res_7676_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(
    mut v_t_7677_: *mut LeanObject,
    mut v___y_7678_: *mut LeanObject,
    mut v___y_7679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_7683_: u8 = 0;
    v___x_7681_ = lean_st_ref_get(v___y_7679_);
    v_infoState_7682_ = lean_ctor_get(v___x_7681_, 7);
    lean_inc_ref(v_infoState_7682_);
    lean_dec(v___x_7681_);
    v_enabled_7683_ = lean_ctor_get_uint8(
        v_infoState_7682_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_7682_);
    if v_enabled_7683_ == 0 {
        let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_7677_);
        v___x_7684_ = lean_box(0);
        v___x_7685_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7685_, 0, v___x_7684_);
        return v___x_7685_;
    } else {
        let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7690_: *mut LeanObject = core::ptr::null_mut();
        v___x_7686_ = lean_unsigned_to_nat(32);
        v___x_7687_ = lean_mk_empty_array_with_capacity(v___x_7686_);
        lean_dec_ref(v___x_7687_);
        v___x_7688_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1,
        );
        v___x_7689_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_7689_, 0, v_t_7677_);
        lean_ctor_set(v___x_7689_, 1, v___x_7688_);
        v___x_7690_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_7689_, v___y_7679_);
        return v___x_7690_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(
    mut v_t_7691_: *mut LeanObject,
    mut v___y_7692_: *mut LeanObject,
    mut v___y_7693_: *mut LeanObject,
    mut v___y_7694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7695_: *mut LeanObject = core::ptr::null_mut();
    v_res_7695_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_7691_, v___y_7692_, v___y_7693_);
    lean_dec(v___y_7693_);
    lean_dec_ref(v___y_7692_);
    return v_res_7695_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    v___x_7696_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_7696_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut LeanObject = core::ptr::null_mut();
    v___x_7697_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_7698_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7698_, 0, v___x_7697_);
    return v___x_7698_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut LeanObject = core::ptr::null_mut();
    v___x_7699_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_7700_ = lean_unsigned_to_nat(0);
    v___x_7701_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_7701_, 0, v___x_7700_);
    lean_ctor_set(v___x_7701_, 1, v___x_7700_);
    lean_ctor_set(v___x_7701_, 2, v___x_7700_);
    lean_ctor_set(v___x_7701_, 3, v___x_7700_);
    lean_ctor_set(v___x_7701_, 4, v___x_7699_);
    lean_ctor_set(v___x_7701_, 5, v___x_7699_);
    lean_ctor_set(v___x_7701_, 6, v___x_7699_);
    lean_ctor_set(v___x_7701_, 7, v___x_7699_);
    lean_ctor_set(v___x_7701_, 8, v___x_7699_);
    lean_ctor_set(v___x_7701_, 9, v___x_7699_);
    return v___x_7701_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    v___x_7702_ = lean_box(1);
    v___x_7703_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ContextInfo_ppGoals___closed__3_once),
        _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3,
    );
    v___x_7704_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_7705_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7705_, 0, v___x_7704_);
    lean_ctor_set(v___x_7705_, 1, v___x_7703_);
    lean_ctor_set(v___x_7705_, 2, v___x_7702_);
    return v___x_7705_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7708_: *mut LeanObject = core::ptr::null_mut();
    v___x_7707_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4;
    v___x_7708_ = l_Lean_stringToMessageData(v___x_7707_);
    return v___x_7708_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    v___x_7710_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_7711_ = l_Lean_stringToMessageData(v___x_7710_);
    return v___x_7711_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut LeanObject = core::ptr::null_mut();
    v___x_7713_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_7714_ = l_Lean_stringToMessageData(v___x_7713_);
    return v___x_7714_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7717_: *mut LeanObject = core::ptr::null_mut();
    v___x_7716_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_7717_ = l_Lean_stringToMessageData(v___x_7716_);
    return v___x_7717_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7720_: *mut LeanObject = core::ptr::null_mut();
    v___x_7719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_7720_ = l_Lean_stringToMessageData(v___x_7719_);
    return v___x_7720_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut LeanObject = core::ptr::null_mut();
    v___x_7722_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_7723_ = l_Lean_stringToMessageData(v___x_7722_);
    return v___x_7723_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut LeanObject = core::ptr::null_mut();
    v___x_7725_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_7726_ = l_Lean_stringToMessageData(v___x_7725_);
    return v___x_7726_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(
    mut v_msg_7727_: *mut LeanObject,
    mut v_declHint_7728_: *mut LeanObject,
    mut v___y_7729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: u8 = 0;
    let mut v_isExporting_7734_: u8 = 0;
    let mut v___x_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: u8 = 0;
    let mut v___x_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7756_: u8 = 0;
    let mut v___x_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7761_: u8 = 0;
    let mut v___x_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7788_: u8 = 0;
    let mut v___x_7789_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7731_ = lean_st_ref_get(v___y_7729_);
                v_env_7732_ = lean_ctor_get(v___x_7731_, 0);
                lean_inc_ref(v_env_7732_);
                lean_dec(v___x_7731_);
                v___x_7733_ = l_Lean_Name_isAnonymous(v_declHint_7728_);
                if v___x_7733_ == 0 {
                    v_isExporting_7734_ = lean_ctor_get_uint8(
                        v_env_7732_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_7734_ == 0 {
                        lean_dec_ref(v_env_7732_);
                        lean_dec(v_declHint_7728_);
                        v___x_7735_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7735_, 0, v_msg_7727_);
                        return v___x_7735_;
                    } else {
                        lean_inc_ref(v_env_7732_);
                        v___x_7736_ = l_Lean_Environment_setExporting(v_env_7732_, v___x_7733_);
                        lean_inc(v_declHint_7728_);
                        lean_inc_ref(v___x_7736_);
                        v___x_7737_ = l_Lean_Environment_contains(
                            v___x_7736_,
                            v_declHint_7728_,
                            v_isExporting_7734_,
                        );
                        if v___x_7737_ == 0 {
                            lean_dec_ref(v___x_7736_);
                            lean_dec_ref(v_env_7732_);
                            lean_dec(v_declHint_7728_);
                            v___x_7738_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_7738_, 0, v_msg_7727_);
                            return v___x_7738_;
                        } else {
                            v___x_7739_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_7740_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
                            v___x_7741_ = l_Lean_Options_empty;
                            v___x_7742_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_7742_, 0, v___x_7736_);
                            lean_ctor_set(v___x_7742_, 1, v___x_7739_);
                            lean_ctor_set(v___x_7742_, 2, v___x_7740_);
                            lean_ctor_set(v___x_7742_, 3, v___x_7741_);
                            lean_inc(v_declHint_7728_);
                            v___x_7743_ =
                                l_Lean_MessageData_ofConstName(v_declHint_7728_, v___x_7733_);
                            v_c_7744_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_7744_, 0, v___x_7742_);
                            lean_ctor_set(v_c_7744_, 1, v___x_7743_);
                            v___x_7745_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_7732_,
                                v_declHint_7728_,
                            );
                            if lean_obj_tag(v___x_7745_) == 0 {
                                lean_dec_ref(v_env_7732_);
                                lean_dec(v_declHint_7728_);
                                v___x_7746_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
                                v___x_7747_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7747_, 0, v___x_7746_);
                                lean_ctor_set(v___x_7747_, 1, v_c_7744_);
                                v___x_7748_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_7749_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7749_, 0, v___x_7747_);
                                lean_ctor_set(v___x_7749_, 1, v___x_7748_);
                                v___x_7750_ = l_Lean_MessageData_note(v___x_7749_);
                                v___x_7751_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7751_, 0, v_msg_7727_);
                                lean_ctor_set(v___x_7751_, 1, v___x_7750_);
                                v___x_7752_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_7752_, 0, v___x_7751_);
                                return v___x_7752_;
                            } else {
                                v_val_7753_ = lean_ctor_get(v___x_7745_, 0);
                                v_isSharedCheck_7788_ = (!lean_is_exclusive(v___x_7745_)) as u8;
                                if v_isSharedCheck_7788_ == 0 {
                                    v___x_7755_ = v___x_7745_;
                                    v_isShared_7756_ = v_isSharedCheck_7788_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_7753_);
                                    lean_dec(v___x_7745_);
                                    v___x_7755_ = lean_box(0);
                                    v_isShared_7756_ = v_isSharedCheck_7788_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_7732_);
                    lean_dec(v_declHint_7728_);
                    v___x_7789_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7789_, 0, v_msg_7727_);
                    return v___x_7789_;
                }
            }
            1 => {
                v___x_7757_ = lean_box(0);
                v___x_7758_ = l_Lean_Environment_header(v_env_7732_);
                lean_dec_ref(v_env_7732_);
                v___x_7759_ = l_Lean_EnvironmentHeader_moduleNames(v___x_7758_);
                v_mod_7760_ = lean_array_get(v___x_7757_, v___x_7759_, v_val_7753_);
                lean_dec(v_val_7753_);
                lean_dec_ref(v___x_7759_);
                v___x_7761_ = l_Lean_isPrivateName(v_declHint_7728_);
                lean_dec(v_declHint_7728_);
                if v___x_7761_ == 0 {
                    v___x_7762_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
                    v___x_7763_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7763_, 0, v___x_7762_);
                    lean_ctor_set(v___x_7763_, 1, v_c_7744_);
                    v___x_7764_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_7765_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7765_, 0, v___x_7763_);
                    lean_ctor_set(v___x_7765_, 1, v___x_7764_);
                    v___x_7766_ = l_Lean_MessageData_ofName(v_mod_7760_);
                    v___x_7767_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7767_, 0, v___x_7765_);
                    lean_ctor_set(v___x_7767_, 1, v___x_7766_);
                    v___x_7768_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_7769_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7769_, 0, v___x_7767_);
                    lean_ctor_set(v___x_7769_, 1, v___x_7768_);
                    v___x_7770_ = l_Lean_MessageData_note(v___x_7769_);
                    v___x_7771_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7771_, 0, v_msg_7727_);
                    lean_ctor_set(v___x_7771_, 1, v___x_7770_);
                    if v_isShared_7756_ == 0 {
                        lean_ctor_set_tag(v___x_7755_, 0);
                        lean_ctor_set(v___x_7755_, 0, v___x_7771_);
                        v___x_7773_ = v___x_7755_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7774_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7774_, 0, v___x_7771_);
                        v___x_7773_ = v_reuseFailAlloc_7774_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7775_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
                    v___x_7776_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7776_, 0, v___x_7775_);
                    lean_ctor_set(v___x_7776_, 1, v_c_7744_);
                    v___x_7777_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_7778_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7778_, 0, v___x_7776_);
                    lean_ctor_set(v___x_7778_, 1, v___x_7777_);
                    v___x_7779_ = l_Lean_MessageData_ofName(v_mod_7760_);
                    v___x_7780_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7780_, 0, v___x_7778_);
                    lean_ctor_set(v___x_7780_, 1, v___x_7779_);
                    v___x_7781_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_7782_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7782_, 0, v___x_7780_);
                    lean_ctor_set(v___x_7782_, 1, v___x_7781_);
                    v___x_7783_ = l_Lean_MessageData_note(v___x_7782_);
                    v___x_7784_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7784_, 0, v_msg_7727_);
                    lean_ctor_set(v___x_7784_, 1, v___x_7783_);
                    if v_isShared_7756_ == 0 {
                        lean_ctor_set_tag(v___x_7755_, 0);
                        lean_ctor_set(v___x_7755_, 0, v___x_7784_);
                        v___x_7786_ = v___x_7755_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7787_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7787_, 0, v___x_7784_);
                        v___x_7786_ = v_reuseFailAlloc_7787_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7773_;
            }
            3 => {
                return v___x_7786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_7790_: *mut LeanObject,
    mut v_declHint_7791_: *mut LeanObject,
    mut v___y_7792_: *mut LeanObject,
    mut v___y_7793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7794_: *mut LeanObject = core::ptr::null_mut();
    v_res_7794_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_7790_, v_declHint_7791_, v___y_7792_);
    lean_dec(v___y_7792_);
    return v_res_7794_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(
    mut v_msg_7795_: *mut LeanObject,
    mut v_declHint_7796_: *mut LeanObject,
    mut v___y_7797_: *mut LeanObject,
    mut v___y_7798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7804_: u8 = 0;
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7800_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_7795_, v_declHint_7796_, v___y_7798_);
                v_a_7801_ = lean_ctor_get(v___x_7800_, 0);
                v_isSharedCheck_7810_ = (!lean_is_exclusive(v___x_7800_)) as u8;
                if v_isSharedCheck_7810_ == 0 {
                    v___x_7803_ = v___x_7800_;
                    v_isShared_7804_ = v_isSharedCheck_7810_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7801_);
                    lean_dec(v___x_7800_);
                    v___x_7803_ = lean_box(0);
                    v_isShared_7804_ = v_isSharedCheck_7810_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7805_ = l_Lean_unknownIdentifierMessageTag;
                v___x_7806_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_7806_, 0, v___x_7805_);
                lean_ctor_set(v___x_7806_, 1, v_a_7801_);
                if v_isShared_7804_ == 0 {
                    lean_ctor_set(v___x_7803_, 0, v___x_7806_);
                    v___x_7808_ = v___x_7803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7809_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7809_, 0, v___x_7806_);
                    v___x_7808_ = v_reuseFailAlloc_7809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(
    mut v_msg_7811_: *mut LeanObject,
    mut v_declHint_7812_: *mut LeanObject,
    mut v___y_7813_: *mut LeanObject,
    mut v___y_7814_: *mut LeanObject,
    mut v___y_7815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7816_: *mut LeanObject = core::ptr::null_mut();
    v_res_7816_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_7811_, v_declHint_7812_, v___y_7813_, v___y_7814_);
    lean_dec(v___y_7814_);
    lean_dec_ref(v___y_7813_);
    return v_res_7816_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(
    mut v_msgData_7817_: *mut LeanObject,
    mut v___y_7818_: *mut LeanObject,
    mut v___y_7819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut LeanObject = core::ptr::null_mut();
    v___x_7821_ = lean_st_ref_get(v___y_7819_);
    v_env_7822_ = lean_ctor_get(v___x_7821_, 0);
    lean_inc_ref(v_env_7822_);
    lean_dec(v___x_7821_);
    v_options_7823_ = lean_ctor_get(v___y_7818_, 2);
    v___x_7824_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
    v___x_7825_ = lean_unsigned_to_nat(32);
    v___x_7826_ = lean_mk_empty_array_with_capacity(v___x_7825_);
    lean_dec_ref(v___x_7826_);
    v___x_7827_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
    lean_inc_ref(v_options_7823_);
    v___x_7828_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_7828_, 0, v_env_7822_);
    lean_ctor_set(v___x_7828_, 1, v___x_7824_);
    lean_ctor_set(v___x_7828_, 2, v___x_7827_);
    lean_ctor_set(v___x_7828_, 3, v_options_7823_);
    v___x_7829_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_7829_, 0, v___x_7828_);
    lean_ctor_set(v___x_7829_, 1, v_msgData_7817_);
    v___x_7830_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7830_, 0, v___x_7829_);
    return v___x_7830_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(
    mut v_msgData_7831_: *mut LeanObject,
    mut v___y_7832_: *mut LeanObject,
    mut v___y_7833_: *mut LeanObject,
    mut v___y_7834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7835_: *mut LeanObject = core::ptr::null_mut();
    v_res_7835_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_7831_, v___y_7832_, v___y_7833_);
    lean_dec(v___y_7833_);
    lean_dec_ref(v___y_7832_);
    return v_res_7835_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(
    mut v_msg_7836_: *mut LeanObject,
    mut v___y_7837_: *mut LeanObject,
    mut v___y_7838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7845_: u8 = 0;
    let mut v___x_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7840_ = lean_ctor_get(v___y_7837_, 5);
                v___x_7841_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_7836_, v___y_7837_, v___y_7838_);
                v_a_7842_ = lean_ctor_get(v___x_7841_, 0);
                v_isSharedCheck_7850_ = (!lean_is_exclusive(v___x_7841_)) as u8;
                if v_isSharedCheck_7850_ == 0 {
                    v___x_7844_ = v___x_7841_;
                    v_isShared_7845_ = v_isSharedCheck_7850_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7842_);
                    lean_dec(v___x_7841_);
                    v___x_7844_ = lean_box(0);
                    v_isShared_7845_ = v_isSharedCheck_7850_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_7840_);
                v___x_7846_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7846_, 0, v_ref_7840_);
                lean_ctor_set(v___x_7846_, 1, v_a_7842_);
                if v_isShared_7845_ == 0 {
                    lean_ctor_set_tag(v___x_7844_, 1);
                    lean_ctor_set(v___x_7844_, 0, v___x_7846_);
                    v___x_7848_ = v___x_7844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7849_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7849_, 0, v___x_7846_);
                    v___x_7848_ = v_reuseFailAlloc_7849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(
    mut v_msg_7851_: *mut LeanObject,
    mut v___y_7852_: *mut LeanObject,
    mut v___y_7853_: *mut LeanObject,
    mut v___y_7854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7855_: *mut LeanObject = core::ptr::null_mut();
    v_res_7855_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_7851_, v___y_7852_, v___y_7853_);
    lean_dec(v___y_7853_);
    lean_dec_ref(v___y_7852_);
    return v_res_7855_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(
    mut v_ref_7856_: *mut LeanObject,
    mut v_msg_7857_: *mut LeanObject,
    mut v___y_7858_: *mut LeanObject,
    mut v___y_7859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7873_: u8 = 0;
    let mut v_cancelTk_x3f_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7875_: u8 = 0;
    let mut v_inheritedTraceOptions_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_7861_ = lean_ctor_get(v___y_7858_, 0);
    v_fileMap_7862_ = lean_ctor_get(v___y_7858_, 1);
    v_options_7863_ = lean_ctor_get(v___y_7858_, 2);
    v_currRecDepth_7864_ = lean_ctor_get(v___y_7858_, 3);
    v_maxRecDepth_7865_ = lean_ctor_get(v___y_7858_, 4);
    v_ref_7866_ = lean_ctor_get(v___y_7858_, 5);
    v_currNamespace_7867_ = lean_ctor_get(v___y_7858_, 6);
    v_openDecls_7868_ = lean_ctor_get(v___y_7858_, 7);
    v_initHeartbeats_7869_ = lean_ctor_get(v___y_7858_, 8);
    v_maxHeartbeats_7870_ = lean_ctor_get(v___y_7858_, 9);
    v_quotContext_7871_ = lean_ctor_get(v___y_7858_, 10);
    v_currMacroScope_7872_ = lean_ctor_get(v___y_7858_, 11);
    v_diag_7873_ = lean_ctor_get_uint8(
        v___y_7858_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_7874_ = lean_ctor_get(v___y_7858_, 12);
    v_suppressElabErrors_7875_ = lean_ctor_get_uint8(
        v___y_7858_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_7876_ = lean_ctor_get(v___y_7858_, 13);
    v_ref_7877_ = l_Lean_replaceRef(v_ref_7856_, v_ref_7866_);
    lean_inc_ref(v_inheritedTraceOptions_7876_);
    lean_inc(v_cancelTk_x3f_7874_);
    lean_inc(v_currMacroScope_7872_);
    lean_inc(v_quotContext_7871_);
    lean_inc(v_maxHeartbeats_7870_);
    lean_inc(v_initHeartbeats_7869_);
    lean_inc(v_openDecls_7868_);
    lean_inc(v_currNamespace_7867_);
    lean_inc(v_maxRecDepth_7865_);
    lean_inc(v_currRecDepth_7864_);
    lean_inc_ref(v_options_7863_);
    lean_inc_ref(v_fileMap_7862_);
    lean_inc_ref(v_fileName_7861_);
    v___x_7878_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_7878_, 0, v_fileName_7861_);
    lean_ctor_set(v___x_7878_, 1, v_fileMap_7862_);
    lean_ctor_set(v___x_7878_, 2, v_options_7863_);
    lean_ctor_set(v___x_7878_, 3, v_currRecDepth_7864_);
    lean_ctor_set(v___x_7878_, 4, v_maxRecDepth_7865_);
    lean_ctor_set(v___x_7878_, 5, v_ref_7877_);
    lean_ctor_set(v___x_7878_, 6, v_currNamespace_7867_);
    lean_ctor_set(v___x_7878_, 7, v_openDecls_7868_);
    lean_ctor_set(v___x_7878_, 8, v_initHeartbeats_7869_);
    lean_ctor_set(v___x_7878_, 9, v_maxHeartbeats_7870_);
    lean_ctor_set(v___x_7878_, 10, v_quotContext_7871_);
    lean_ctor_set(v___x_7878_, 11, v_currMacroScope_7872_);
    lean_ctor_set(v___x_7878_, 12, v_cancelTk_x3f_7874_);
    lean_ctor_set(v___x_7878_, 13, v_inheritedTraceOptions_7876_);
    lean_ctor_set_uint8(
        v___x_7878_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_7873_,
    );
    lean_ctor_set_uint8(
        v___x_7878_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_7875_,
    );
    v___x_7879_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_7857_, v___x_7878_, v___y_7859_);
    lean_dec_ref_known(v___x_7878_, 14);
    return v___x_7879_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_ref_7880_: *mut LeanObject,
    mut v_msg_7881_: *mut LeanObject,
    mut v___y_7882_: *mut LeanObject,
    mut v___y_7883_: *mut LeanObject,
    mut v___y_7884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7885_: *mut LeanObject = core::ptr::null_mut();
    v_res_7885_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_7880_, v_msg_7881_, v___y_7882_, v___y_7883_);
    lean_dec(v___y_7883_);
    lean_dec_ref(v___y_7882_);
    lean_dec(v_ref_7880_);
    return v_res_7885_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(
    mut v_ref_7886_: *mut LeanObject,
    mut v_msg_7887_: *mut LeanObject,
    mut v_declHint_7888_: *mut LeanObject,
    mut v___y_7889_: *mut LeanObject,
    mut v___y_7890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: *mut LeanObject = core::ptr::null_mut();
    v___x_7892_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_7887_, v_declHint_7888_, v___y_7889_, v___y_7890_);
    v_a_7893_ = lean_ctor_get(v___x_7892_, 0);
    lean_inc(v_a_7893_);
    lean_dec_ref(v___x_7892_);
    v___x_7894_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_7886_, v_a_7893_, v___y_7889_, v___y_7890_);
    return v___x_7894_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(
    mut v_ref_7895_: *mut LeanObject,
    mut v_msg_7896_: *mut LeanObject,
    mut v_declHint_7897_: *mut LeanObject,
    mut v___y_7898_: *mut LeanObject,
    mut v___y_7899_: *mut LeanObject,
    mut v___y_7900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7901_: *mut LeanObject = core::ptr::null_mut();
    v_res_7901_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_7895_, v_msg_7896_, v_declHint_7897_, v___y_7898_, v___y_7899_);
    lean_dec(v___y_7899_);
    lean_dec_ref(v___y_7898_);
    lean_dec(v_ref_7895_);
    return v_res_7901_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7904_: *mut LeanObject = core::ptr::null_mut();
    v___x_7903_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
    v___x_7904_ = l_Lean_stringToMessageData(v___x_7903_);
    return v___x_7904_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: *mut LeanObject = core::ptr::null_mut();
    v___x_7906_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2;
    v___x_7907_ = l_Lean_stringToMessageData(v___x_7906_);
    return v___x_7907_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_ref_7908_: *mut LeanObject,
    mut v_constName_7909_: *mut LeanObject,
    mut v___y_7910_: *mut LeanObject,
    mut v___y_7911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: u8 = 0;
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut LeanObject = core::ptr::null_mut();
    v___x_7913_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
    v___x_7914_ = 0;
    lean_inc(v_constName_7909_);
    v___x_7915_ = l_Lean_MessageData_ofConstName(v_constName_7909_, v___x_7914_);
    v___x_7916_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7916_, 0, v___x_7913_);
    lean_ctor_set(v___x_7916_, 1, v___x_7915_);
    v___x_7917_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
    v___x_7918_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7918_, 0, v___x_7916_);
    lean_ctor_set(v___x_7918_, 1, v___x_7917_);
    v___x_7919_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_7908_, v___x_7918_, v_constName_7909_, v___y_7910_, v___y_7911_);
    return v___x_7919_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_ref_7920_: *mut LeanObject,
    mut v_constName_7921_: *mut LeanObject,
    mut v___y_7922_: *mut LeanObject,
    mut v___y_7923_: *mut LeanObject,
    mut v___y_7924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7925_: *mut LeanObject = core::ptr::null_mut();
    v_res_7925_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_7920_, v_constName_7921_, v___y_7922_, v___y_7923_);
    lean_dec(v___y_7923_);
    lean_dec_ref(v___y_7922_);
    lean_dec(v_ref_7920_);
    return v_res_7925_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_constName_7926_: *mut LeanObject,
    mut v___y_7927_: *mut LeanObject,
    mut v___y_7928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut LeanObject = core::ptr::null_mut();
    v_ref_7930_ = lean_ctor_get(v___y_7927_, 5);
    v___x_7931_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_7930_, v_constName_7926_, v___y_7927_, v___y_7928_);
    return v___x_7931_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_constName_7932_: *mut LeanObject,
    mut v___y_7933_: *mut LeanObject,
    mut v___y_7934_: *mut LeanObject,
    mut v___y_7935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7936_: *mut LeanObject = core::ptr::null_mut();
    v_res_7936_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_7932_, v___y_7933_, v___y_7934_);
    lean_dec(v___y_7934_);
    lean_dec_ref(v___y_7933_);
    return v_res_7936_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(
    mut v_constName_7937_: *mut LeanObject,
    mut v___y_7938_: *mut LeanObject,
    mut v___y_7939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7943_: u8 = 0;
    let mut v___x_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7949_: u8 = 0;
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7941_ = lean_st_ref_get(v___y_7939_);
                v_env_7942_ = lean_ctor_get(v___x_7941_, 0);
                lean_inc_ref(v_env_7942_);
                lean_dec(v___x_7941_);
                v___x_7943_ = 0;
                lean_inc(v_constName_7937_);
                v___x_7944_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_7942_,
                    v_constName_7937_,
                    v___x_7943_,
                );
                if lean_obj_tag(v___x_7944_) == 0 {
                    v___x_7945_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_7937_, v___y_7938_, v___y_7939_);
                    return v___x_7945_;
                } else {
                    lean_dec(v_constName_7937_);
                    v_val_7946_ = lean_ctor_get(v___x_7944_, 0);
                    v_isSharedCheck_7953_ = (!lean_is_exclusive(v___x_7944_)) as u8;
                    if v_isSharedCheck_7953_ == 0 {
                        v___x_7948_ = v___x_7944_;
                        v_isShared_7949_ = v_isSharedCheck_7953_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7946_);
                        lean_dec(v___x_7944_);
                        v___x_7948_ = lean_box(0);
                        v_isShared_7949_ = v_isSharedCheck_7953_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7949_ == 0 {
                    lean_ctor_set_tag(v___x_7948_, 0);
                    v___x_7951_ = v___x_7948_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7952_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7952_, 0, v_val_7946_);
                    v___x_7951_ = v_reuseFailAlloc_7952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(
    mut v_constName_7954_: *mut LeanObject,
    mut v___y_7955_: *mut LeanObject,
    mut v___y_7956_: *mut LeanObject,
    mut v___y_7957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7958_: *mut LeanObject = core::ptr::null_mut();
    v_res_7958_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_7954_, v___y_7955_, v___y_7956_);
    lean_dec(v___y_7956_);
    lean_dec_ref(v___y_7955_);
    return v_res_7958_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(
    mut v_a_7959_: *mut LeanObject,
    mut v_a_7960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7966_: u8 = 0;
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_7959_) == 0 {
                    v___x_7961_ = l_List_reverse___redArg(v_a_7960_);
                    return v___x_7961_;
                } else {
                    v_head_7962_ = lean_ctor_get(v_a_7959_, 0);
                    v_tail_7963_ = lean_ctor_get(v_a_7959_, 1);
                    v_isSharedCheck_7972_ = (!lean_is_exclusive(v_a_7959_)) as u8;
                    if v_isSharedCheck_7972_ == 0 {
                        v___x_7965_ = v_a_7959_;
                        v_isShared_7966_ = v_isSharedCheck_7972_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7963_);
                        lean_inc(v_head_7962_);
                        lean_dec(v_a_7959_);
                        v___x_7965_ = lean_box(0);
                        v_isShared_7966_ = v_isSharedCheck_7972_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7967_ = l_Lean_mkLevelParam(v_head_7962_);
                if v_isShared_7966_ == 0 {
                    lean_ctor_set(v___x_7965_, 1, v_a_7960_);
                    lean_ctor_set(v___x_7965_, 0, v___x_7967_);
                    v___x_7969_ = v___x_7965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7971_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7971_, 0, v___x_7967_);
                    lean_ctor_set(v_reuseFailAlloc_7971_, 1, v_a_7960_);
                    v___x_7969_ = v_reuseFailAlloc_7971_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_7959_ = v_tail_7963_;
                v_a_7960_ = v___x_7969_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(
    mut v_constName_7973_: *mut LeanObject,
    mut v___y_7974_: *mut LeanObject,
    mut v___y_7975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7981_: u8 = 0;
    let mut v_levelParams_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7989_: u8 = 0;
    let mut v_a_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7993_: u8 = 0;
    let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_7973_);
                v___x_7977_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_7973_, v___y_7974_, v___y_7975_);
                if lean_obj_tag(v___x_7977_) == 0 {
                    v_a_7978_ = lean_ctor_get(v___x_7977_, 0);
                    v_isSharedCheck_7989_ = (!lean_is_exclusive(v___x_7977_)) as u8;
                    if v_isSharedCheck_7989_ == 0 {
                        v___x_7980_ = v___x_7977_;
                        v_isShared_7981_ = v_isSharedCheck_7989_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7978_);
                        lean_dec(v___x_7977_);
                        v___x_7980_ = lean_box(0);
                        v_isShared_7981_ = v_isSharedCheck_7989_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_7973_);
                    v_a_7990_ = lean_ctor_get(v___x_7977_, 0);
                    v_isSharedCheck_7997_ = (!lean_is_exclusive(v___x_7977_)) as u8;
                    if v_isSharedCheck_7997_ == 0 {
                        v___x_7992_ = v___x_7977_;
                        v_isShared_7993_ = v_isSharedCheck_7997_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7990_);
                        lean_dec(v___x_7977_);
                        v___x_7992_ = lean_box(0);
                        v_isShared_7993_ = v_isSharedCheck_7997_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_7982_ = lean_ctor_get(v_a_7978_, 1);
                lean_inc(v_levelParams_7982_);
                lean_dec(v_a_7978_);
                v___x_7983_ = lean_box(0);
                v___x_7984_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_7982_, v___x_7983_);
                v___x_7985_ = l_Lean_mkConst(v_constName_7973_, v___x_7984_);
                if v_isShared_7981_ == 0 {
                    lean_ctor_set(v___x_7980_, 0, v___x_7985_);
                    v___x_7987_ = v___x_7980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7988_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7988_, 0, v___x_7985_);
                    v___x_7987_ = v_reuseFailAlloc_7988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7987_;
            }
            3 => {
                if v_isShared_7993_ == 0 {
                    v___x_7995_ = v___x_7992_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7996_, 0, v_a_7990_);
                    v___x_7995_ = v_reuseFailAlloc_7996_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(
    mut v_constName_7998_: *mut LeanObject,
    mut v___y_7999_: *mut LeanObject,
    mut v___y_8000_: *mut LeanObject,
    mut v___y_8001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8002_: *mut LeanObject = core::ptr::null_mut();
    v_res_8002_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_7998_, v___y_7999_, v___y_8000_);
    lean_dec(v___y_8000_);
    lean_dec_ref(v___y_7999_);
    return v_res_8002_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(
    mut v_stx_8003_: *mut LeanObject,
    mut v_n_8004_: *mut LeanObject,
    mut v_expectedType_x3f_8005_: *mut LeanObject,
    mut v___y_8006_: *mut LeanObject,
    mut v___y_8007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8014_: u8 = 0;
    let mut v___x_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8021_: u8 = 0;
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8009_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_8004_, v___y_8006_, v___y_8007_);
                if lean_obj_tag(v___x_8009_) == 0 {
                    v_a_8010_ = lean_ctor_get(v___x_8009_, 0);
                    lean_inc(v_a_8010_);
                    lean_dec_ref_known(v___x_8009_, 1);
                    v___x_8011_ = lean_box(0);
                    v___x_8012_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8012_, 0, v___x_8011_);
                    lean_ctor_set(v___x_8012_, 1, v_stx_8003_);
                    v___x_8013_ = l_Lean_LocalContext_empty;
                    v___x_8014_ = 0;
                    v___x_8015_ = lean_alloc_ctor(0, 4, (2) as u32);
                    lean_ctor_set(v___x_8015_, 0, v___x_8012_);
                    lean_ctor_set(v___x_8015_, 1, v___x_8013_);
                    lean_ctor_set(v___x_8015_, 2, v_expectedType_x3f_8005_);
                    lean_ctor_set(v___x_8015_, 3, v_a_8010_);
                    lean_ctor_set_uint8(
                        v___x_8015_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_8014_,
                    );
                    lean_ctor_set_uint8(
                        v___x_8015_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v___x_8014_,
                    );
                    v___x_8016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8016_, 0, v___x_8015_);
                    v___x_8017_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_8016_, v___y_8006_, v___y_8007_);
                    return v___x_8017_;
                } else {
                    lean_dec(v_expectedType_x3f_8005_);
                    lean_dec(v_stx_8003_);
                    v_a_8018_ = lean_ctor_get(v___x_8009_, 0);
                    v_isSharedCheck_8025_ = (!lean_is_exclusive(v___x_8009_)) as u8;
                    if v_isSharedCheck_8025_ == 0 {
                        v___x_8020_ = v___x_8009_;
                        v_isShared_8021_ = v_isSharedCheck_8025_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8018_);
                        lean_dec(v___x_8009_);
                        v___x_8020_ = lean_box(0);
                        v_isShared_8021_ = v_isSharedCheck_8025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8021_ == 0 {
                    v___x_8023_ = v___x_8020_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8024_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8024_, 0, v_a_8018_);
                    v___x_8023_ = v_reuseFailAlloc_8024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(
    mut v_stx_8026_: *mut LeanObject,
    mut v_n_8027_: *mut LeanObject,
    mut v_expectedType_x3f_8028_: *mut LeanObject,
    mut v___y_8029_: *mut LeanObject,
    mut v___y_8030_: *mut LeanObject,
    mut v___y_8031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8032_: *mut LeanObject = core::ptr::null_mut();
    v_res_8032_ =
        l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(
            v_stx_8026_,
            v_n_8027_,
            v_expectedType_x3f_8028_,
            v___y_8029_,
            v___y_8030_,
        );
    lean_dec(v___y_8030_);
    lean_dec_ref(v___y_8029_);
    return v_res_8032_;
}
pub unsafe fn l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
    mut v_id_8033_: *mut LeanObject,
    mut v_expectedType_x3f_8034_: *mut LeanObject,
    mut v_a_8035_: *mut LeanObject,
    mut v_a_8036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8042_: u8 = 0;
    let mut v___x_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_8044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_8045_: u8 = 0;
    let mut v___x_8047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8052_: u8 = 0;
    let mut v___x_8054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8056_: u8 = 0;
    let mut v_unused_8057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8061_: u8 = 0;
    let mut v___x_8063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8065_: u8 = 0;
    let mut v_isSharedCheck_8066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_id_8033_);
                v___x_8038_ = l_Lean_realizeGlobalConstNoOverload(v_id_8033_, v_a_8035_, v_a_8036_);
                if lean_obj_tag(v___x_8038_) == 0 {
                    v_a_8039_ = lean_ctor_get(v___x_8038_, 0);
                    v_isSharedCheck_8066_ = (!lean_is_exclusive(v___x_8038_)) as u8;
                    if v_isSharedCheck_8066_ == 0 {
                        v___x_8041_ = v___x_8038_;
                        v_isShared_8042_ = v_isSharedCheck_8066_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8039_);
                        lean_dec(v___x_8038_);
                        v___x_8041_ = lean_box(0);
                        v_isShared_8042_ = v_isSharedCheck_8066_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_expectedType_x3f_8034_);
                    lean_dec(v_id_8033_);
                    return v___x_8038_;
                }
            }
            1 => {
                v___x_8043_ = lean_st_ref_get(v_a_8036_);
                v_infoState_8044_ = lean_ctor_get(v___x_8043_, 7);
                lean_inc_ref(v_infoState_8044_);
                lean_dec(v___x_8043_);
                v_enabled_8045_ = lean_ctor_get_uint8(
                    v_infoState_8044_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_8044_);
                if v_enabled_8045_ == 0 {
                    lean_dec(v_expectedType_x3f_8034_);
                    lean_dec(v_id_8033_);
                    if v_isShared_8042_ == 0 {
                        v___x_8047_ = v___x_8041_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8048_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8048_, 0, v_a_8039_);
                        v___x_8047_ = v_reuseFailAlloc_8048_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8041_);
                    lean_inc(v_a_8039_);
                    v___x_8049_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_8033_, v_a_8039_, v_expectedType_x3f_8034_, v_a_8035_, v_a_8036_);
                    if lean_obj_tag(v___x_8049_) == 0 {
                        v_isSharedCheck_8056_ = (!lean_is_exclusive(v___x_8049_)) as u8;
                        if v_isSharedCheck_8056_ == 0 {
                            v_unused_8057_ = lean_ctor_get(v___x_8049_, 0);
                            lean_dec(v_unused_8057_);
                            v___x_8051_ = v___x_8049_;
                            v_isShared_8052_ = v_isSharedCheck_8056_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_8049_);
                            v___x_8051_ = lean_box(0);
                            v_isShared_8052_ = v_isSharedCheck_8056_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8039_);
                        v_a_8058_ = lean_ctor_get(v___x_8049_, 0);
                        v_isSharedCheck_8065_ = (!lean_is_exclusive(v___x_8049_)) as u8;
                        if v_isSharedCheck_8065_ == 0 {
                            v___x_8060_ = v___x_8049_;
                            v_isShared_8061_ = v_isSharedCheck_8065_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_8058_);
                            lean_dec(v___x_8049_);
                            v___x_8060_ = lean_box(0);
                            v_isShared_8061_ = v_isSharedCheck_8065_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8047_;
            }
            3 => {
                if v_isShared_8052_ == 0 {
                    lean_ctor_set(v___x_8051_, 0, v_a_8039_);
                    v___x_8054_ = v___x_8051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8055_, 0, v_a_8039_);
                    v___x_8054_ = v_reuseFailAlloc_8055_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8054_;
            }
            5 => {
                if v_isShared_8061_ == 0 {
                    v___x_8063_ = v___x_8060_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8064_, 0, v_a_8058_);
                    v___x_8063_ = v_reuseFailAlloc_8064_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(
    mut v_id_8067_: *mut LeanObject,
    mut v_expectedType_x3f_8068_: *mut LeanObject,
    mut v_a_8069_: *mut LeanObject,
    mut v_a_8070_: *mut LeanObject,
    mut v_a_8071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8072_: *mut LeanObject = core::ptr::null_mut();
    v_res_8072_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
        v_id_8067_,
        v_expectedType_x3f_8068_,
        v_a_8069_,
        v_a_8070_,
    );
    lean_dec(v_a_8070_);
    lean_dec_ref(v_a_8069_);
    return v_res_8072_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(
    mut v_t_8073_: *mut LeanObject,
    mut v___y_8074_: *mut LeanObject,
    mut v___y_8075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8077_: *mut LeanObject = core::ptr::null_mut();
    v___x_8077_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_8073_, v___y_8075_);
    return v___x_8077_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(
    mut v_t_8078_: *mut LeanObject,
    mut v___y_8079_: *mut LeanObject,
    mut v___y_8080_: *mut LeanObject,
    mut v___y_8081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8082_: *mut LeanObject = core::ptr::null_mut();
    v_res_8082_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_8078_, v___y_8079_, v___y_8080_);
    lean_dec(v___y_8080_);
    lean_dec_ref(v___y_8079_);
    return v_res_8082_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_8083_: *mut LeanObject,
    mut v_constName_8084_: *mut LeanObject,
    mut v___y_8085_: *mut LeanObject,
    mut v___y_8086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8088_: *mut LeanObject = core::ptr::null_mut();
    v___x_8088_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_8084_, v___y_8085_, v___y_8086_);
    return v___x_8088_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_8089_: *mut LeanObject,
    mut v_constName_8090_: *mut LeanObject,
    mut v___y_8091_: *mut LeanObject,
    mut v___y_8092_: *mut LeanObject,
    mut v___y_8093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8094_: *mut LeanObject = core::ptr::null_mut();
    v_res_8094_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_8089_, v_constName_8090_, v___y_8091_, v___y_8092_);
    lean_dec(v___y_8092_);
    lean_dec_ref(v___y_8091_);
    return v_res_8094_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b1_8095_: *mut LeanObject,
    mut v_ref_8096_: *mut LeanObject,
    mut v_constName_8097_: *mut LeanObject,
    mut v___y_8098_: *mut LeanObject,
    mut v___y_8099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    v___x_8101_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_8096_, v_constName_8097_, v___y_8098_, v___y_8099_);
    return v___x_8101_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b1_8102_: *mut LeanObject,
    mut v_ref_8103_: *mut LeanObject,
    mut v_constName_8104_: *mut LeanObject,
    mut v___y_8105_: *mut LeanObject,
    mut v___y_8106_: *mut LeanObject,
    mut v___y_8107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8108_: *mut LeanObject = core::ptr::null_mut();
    v_res_8108_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_8102_, v_ref_8103_, v_constName_8104_, v___y_8105_, v___y_8106_);
    lean_dec(v___y_8106_);
    lean_dec_ref(v___y_8105_);
    lean_dec(v_ref_8103_);
    return v_res_8108_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(
    mut v_00_u03b1_8109_: *mut LeanObject,
    mut v_ref_8110_: *mut LeanObject,
    mut v_msg_8111_: *mut LeanObject,
    mut v_declHint_8112_: *mut LeanObject,
    mut v___y_8113_: *mut LeanObject,
    mut v___y_8114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8116_: *mut LeanObject = core::ptr::null_mut();
    v___x_8116_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_8110_, v_msg_8111_, v_declHint_8112_, v___y_8113_, v___y_8114_);
    return v___x_8116_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b1_8117_: *mut LeanObject,
    mut v_ref_8118_: *mut LeanObject,
    mut v_msg_8119_: *mut LeanObject,
    mut v_declHint_8120_: *mut LeanObject,
    mut v___y_8121_: *mut LeanObject,
    mut v___y_8122_: *mut LeanObject,
    mut v___y_8123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8124_: *mut LeanObject = core::ptr::null_mut();
    v_res_8124_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_8117_, v_ref_8118_, v_msg_8119_, v_declHint_8120_, v___y_8121_, v___y_8122_);
    lean_dec(v___y_8122_);
    lean_dec_ref(v___y_8121_);
    lean_dec(v_ref_8118_);
    return v_res_8124_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(
    mut v_msg_8125_: *mut LeanObject,
    mut v_declHint_8126_: *mut LeanObject,
    mut v___y_8127_: *mut LeanObject,
    mut v___y_8128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8130_: *mut LeanObject = core::ptr::null_mut();
    v___x_8130_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_8125_, v_declHint_8126_, v___y_8128_);
    return v___x_8130_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(
    mut v_msg_8131_: *mut LeanObject,
    mut v_declHint_8132_: *mut LeanObject,
    mut v___y_8133_: *mut LeanObject,
    mut v___y_8134_: *mut LeanObject,
    mut v___y_8135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8136_: *mut LeanObject = core::ptr::null_mut();
    v_res_8136_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_8131_, v_declHint_8132_, v___y_8133_, v___y_8134_);
    lean_dec(v___y_8134_);
    lean_dec_ref(v___y_8133_);
    return v_res_8136_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(
    mut v_00_u03b1_8137_: *mut LeanObject,
    mut v_ref_8138_: *mut LeanObject,
    mut v_msg_8139_: *mut LeanObject,
    mut v___y_8140_: *mut LeanObject,
    mut v___y_8141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8143_: *mut LeanObject = core::ptr::null_mut();
    v___x_8143_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_8138_, v_msg_8139_, v___y_8140_, v___y_8141_);
    return v___x_8143_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_8144_: *mut LeanObject,
    mut v_ref_8145_: *mut LeanObject,
    mut v_msg_8146_: *mut LeanObject,
    mut v___y_8147_: *mut LeanObject,
    mut v___y_8148_: *mut LeanObject,
    mut v___y_8149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8150_: *mut LeanObject = core::ptr::null_mut();
    v_res_8150_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_8144_, v_ref_8145_, v_msg_8146_, v___y_8147_, v___y_8148_);
    lean_dec(v___y_8148_);
    lean_dec_ref(v___y_8147_);
    lean_dec(v_ref_8145_);
    return v_res_8150_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(
    mut v_00_u03b1_8151_: *mut LeanObject,
    mut v_msg_8152_: *mut LeanObject,
    mut v___y_8153_: *mut LeanObject,
    mut v___y_8154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8156_: *mut LeanObject = core::ptr::null_mut();
    v___x_8156_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_8152_, v___y_8153_, v___y_8154_);
    return v___x_8156_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(
    mut v_00_u03b1_8157_: *mut LeanObject,
    mut v_msg_8158_: *mut LeanObject,
    mut v___y_8159_: *mut LeanObject,
    mut v___y_8160_: *mut LeanObject,
    mut v___y_8161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8162_: *mut LeanObject = core::ptr::null_mut();
    v_res_8162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_8157_, v_msg_8158_, v___y_8159_, v___y_8160_);
    lean_dec(v___y_8160_);
    lean_dec_ref(v___y_8159_);
    return v_res_8162_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(
    mut v_id_8163_: *mut LeanObject,
    mut v_expectedType_x3f_8164_: *mut LeanObject,
    mut v_as_x27_8165_: *mut LeanObject,
    mut v_b_8166_: *mut LeanObject,
    mut v___y_8167_: *mut LeanObject,
    mut v___y_8168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8174_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_8165_) == 0 {
                    lean_dec(v_expectedType_x3f_8164_);
                    lean_dec(v_id_8163_);
                    v___x_8170_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8170_, 0, v_b_8166_);
                    return v___x_8170_;
                } else {
                    v_head_8171_ = lean_ctor_get(v_as_x27_8165_, 0);
                    v_tail_8172_ = lean_ctor_get(v_as_x27_8165_, 1);
                    lean_inc(v_expectedType_x3f_8164_);
                    lean_inc(v_head_8171_);
                    lean_inc(v_id_8163_);
                    v___x_8173_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_8163_, v_head_8171_, v_expectedType_x3f_8164_, v___y_8167_, v___y_8168_);
                    if lean_obj_tag(v___x_8173_) == 0 {
                        lean_dec_ref_known(v___x_8173_, 1);
                        v___x_8174_ = lean_box(0);
                        v_as_x27_8165_ = v_tail_8172_;
                        v_b_8166_ = v___x_8174_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_expectedType_x3f_8164_);
                        lean_dec(v_id_8163_);
                        return v___x_8173_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(
    mut v_id_8176_: *mut LeanObject,
    mut v_expectedType_x3f_8177_: *mut LeanObject,
    mut v_as_x27_8178_: *mut LeanObject,
    mut v_b_8179_: *mut LeanObject,
    mut v___y_8180_: *mut LeanObject,
    mut v___y_8181_: *mut LeanObject,
    mut v___y_8182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8183_: *mut LeanObject = core::ptr::null_mut();
    v_res_8183_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(
            v_id_8176_,
            v_expectedType_x3f_8177_,
            v_as_x27_8178_,
            v_b_8179_,
            v___y_8180_,
            v___y_8181_,
        );
    lean_dec(v___y_8181_);
    lean_dec_ref(v___y_8180_);
    lean_dec(v_as_x27_8178_);
    return v_res_8183_;
}
pub unsafe fn l_Lean_Elab_realizeGlobalConstWithInfos(
    mut v_id_8184_: *mut LeanObject,
    mut v_expectedType_x3f_8185_: *mut LeanObject,
    mut v_a_8186_: *mut LeanObject,
    mut v_a_8187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8193_: u8 = 0;
    let mut v___x_8194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_8195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_8196_: u8 = 0;
    let mut v___x_8198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8204_: u8 = 0;
    let mut v___x_8206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8208_: u8 = 0;
    let mut v_unused_8209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8213_: u8 = 0;
    let mut v___x_8215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8217_: u8 = 0;
    let mut v_isSharedCheck_8218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_id_8184_);
                v___x_8189_ = l_Lean_realizeGlobalConst(v_id_8184_, v_a_8186_, v_a_8187_);
                if lean_obj_tag(v___x_8189_) == 0 {
                    v_a_8190_ = lean_ctor_get(v___x_8189_, 0);
                    v_isSharedCheck_8218_ = (!lean_is_exclusive(v___x_8189_)) as u8;
                    if v_isSharedCheck_8218_ == 0 {
                        v___x_8192_ = v___x_8189_;
                        v_isShared_8193_ = v_isSharedCheck_8218_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8190_);
                        lean_dec(v___x_8189_);
                        v___x_8192_ = lean_box(0);
                        v_isShared_8193_ = v_isSharedCheck_8218_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_expectedType_x3f_8185_);
                    lean_dec(v_id_8184_);
                    return v___x_8189_;
                }
            }
            1 => {
                v___x_8194_ = lean_st_ref_get(v_a_8187_);
                v_infoState_8195_ = lean_ctor_get(v___x_8194_, 7);
                lean_inc_ref(v_infoState_8195_);
                lean_dec(v___x_8194_);
                v_enabled_8196_ = lean_ctor_get_uint8(
                    v_infoState_8195_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_8195_);
                if v_enabled_8196_ == 0 {
                    lean_dec(v_expectedType_x3f_8185_);
                    lean_dec(v_id_8184_);
                    if v_isShared_8193_ == 0 {
                        v___x_8198_ = v___x_8192_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8199_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8199_, 0, v_a_8190_);
                        v___x_8198_ = v_reuseFailAlloc_8199_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8192_);
                    v___x_8200_ = lean_box(0);
                    v___x_8201_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_8184_, v_expectedType_x3f_8185_, v_a_8190_, v___x_8200_, v_a_8186_, v_a_8187_);
                    if lean_obj_tag(v___x_8201_) == 0 {
                        v_isSharedCheck_8208_ = (!lean_is_exclusive(v___x_8201_)) as u8;
                        if v_isSharedCheck_8208_ == 0 {
                            v_unused_8209_ = lean_ctor_get(v___x_8201_, 0);
                            lean_dec(v_unused_8209_);
                            v___x_8203_ = v___x_8201_;
                            v_isShared_8204_ = v_isSharedCheck_8208_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_8201_);
                            v___x_8203_ = lean_box(0);
                            v_isShared_8204_ = v_isSharedCheck_8208_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8190_);
                        v_a_8210_ = lean_ctor_get(v___x_8201_, 0);
                        v_isSharedCheck_8217_ = (!lean_is_exclusive(v___x_8201_)) as u8;
                        if v_isSharedCheck_8217_ == 0 {
                            v___x_8212_ = v___x_8201_;
                            v_isShared_8213_ = v_isSharedCheck_8217_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_8210_);
                            lean_dec(v___x_8201_);
                            v___x_8212_ = lean_box(0);
                            v_isShared_8213_ = v_isSharedCheck_8217_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8198_;
            }
            3 => {
                if v_isShared_8204_ == 0 {
                    lean_ctor_set(v___x_8203_, 0, v_a_8190_);
                    v___x_8206_ = v___x_8203_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8207_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8207_, 0, v_a_8190_);
                    v___x_8206_ = v_reuseFailAlloc_8207_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8206_;
            }
            5 => {
                if v_isShared_8213_ == 0 {
                    v___x_8215_ = v___x_8212_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8216_, 0, v_a_8210_);
                    v___x_8215_ = v_reuseFailAlloc_8216_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_realizeGlobalConstWithInfos___boxed(
    mut v_id_8219_: *mut LeanObject,
    mut v_expectedType_x3f_8220_: *mut LeanObject,
    mut v_a_8221_: *mut LeanObject,
    mut v_a_8222_: *mut LeanObject,
    mut v_a_8223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8224_: *mut LeanObject = core::ptr::null_mut();
    v_res_8224_ = l_Lean_Elab_realizeGlobalConstWithInfos(
        v_id_8219_,
        v_expectedType_x3f_8220_,
        v_a_8221_,
        v_a_8222_,
    );
    lean_dec(v_a_8222_);
    lean_dec_ref(v_a_8221_);
    return v_res_8224_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(
    mut v_id_8225_: *mut LeanObject,
    mut v_expectedType_x3f_8226_: *mut LeanObject,
    mut v_as_8227_: *mut LeanObject,
    mut v_as_x27_8228_: *mut LeanObject,
    mut v_b_8229_: *mut LeanObject,
    mut v_a_8230_: *mut LeanObject,
    mut v___y_8231_: *mut LeanObject,
    mut v___y_8232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8234_: *mut LeanObject = core::ptr::null_mut();
    v___x_8234_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(
            v_id_8225_,
            v_expectedType_x3f_8226_,
            v_as_x27_8228_,
            v_b_8229_,
            v___y_8231_,
            v___y_8232_,
        );
    return v___x_8234_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(
    mut v_id_8235_: *mut LeanObject,
    mut v_expectedType_x3f_8236_: *mut LeanObject,
    mut v_as_8237_: *mut LeanObject,
    mut v_as_x27_8238_: *mut LeanObject,
    mut v_b_8239_: *mut LeanObject,
    mut v_a_8240_: *mut LeanObject,
    mut v___y_8241_: *mut LeanObject,
    mut v___y_8242_: *mut LeanObject,
    mut v___y_8243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8244_: *mut LeanObject = core::ptr::null_mut();
    v_res_8244_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(
        v_id_8235_,
        v_expectedType_x3f_8236_,
        v_as_8237_,
        v_as_x27_8238_,
        v_b_8239_,
        v_a_8240_,
        v___y_8241_,
        v___y_8242_,
    );
    lean_dec(v___y_8242_);
    lean_dec_ref(v___y_8241_);
    lean_dec(v_as_x27_8238_);
    lean_dec(v_as_8237_);
    return v_res_8244_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(
    mut v_ref_8245_: *mut LeanObject,
    mut v_as_x27_8246_: *mut LeanObject,
    mut v_b_8247_: *mut LeanObject,
    mut v___y_8248_: *mut LeanObject,
    mut v___y_8249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_8246_) == 0 {
                    lean_dec(v_ref_8245_);
                    v___x_8251_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8251_, 0, v_b_8247_);
                    return v___x_8251_;
                } else {
                    v_head_8252_ = lean_ctor_get(v_as_x27_8246_, 0);
                    v_tail_8253_ = lean_ctor_get(v_as_x27_8246_, 1);
                    v_fst_8254_ = lean_ctor_get(v_head_8252_, 0);
                    v___x_8255_ = lean_box(0);
                    lean_inc(v_fst_8254_);
                    lean_inc(v_ref_8245_);
                    v___x_8256_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_8245_, v_fst_8254_, v___x_8255_, v___y_8248_, v___y_8249_);
                    if lean_obj_tag(v___x_8256_) == 0 {
                        lean_dec_ref_known(v___x_8256_, 1);
                        v___x_8257_ = lean_box(0);
                        v_as_x27_8246_ = v_tail_8253_;
                        v_b_8247_ = v___x_8257_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_ref_8245_);
                        return v___x_8256_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(
    mut v_ref_8259_: *mut LeanObject,
    mut v_as_x27_8260_: *mut LeanObject,
    mut v_b_8261_: *mut LeanObject,
    mut v___y_8262_: *mut LeanObject,
    mut v___y_8263_: *mut LeanObject,
    mut v___y_8264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8265_: *mut LeanObject = core::ptr::null_mut();
    v_res_8265_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(
            v_ref_8259_,
            v_as_x27_8260_,
            v_b_8261_,
            v___y_8262_,
            v___y_8263_,
        );
    lean_dec(v___y_8263_);
    lean_dec_ref(v___y_8262_);
    lean_dec(v_as_x27_8260_);
    return v_res_8265_;
}
pub unsafe fn l_Lean_Elab_realizeGlobalNameWithInfos(
    mut v_ref_8266_: *mut LeanObject,
    mut v_id_8267_: *mut LeanObject,
    mut v_a_8268_: *mut LeanObject,
    mut v_a_8269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8275_: u8 = 0;
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_8278_: u8 = 0;
    let mut v___x_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8286_: u8 = 0;
    let mut v___x_8288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8290_: u8 = 0;
    let mut v_unused_8291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8295_: u8 = 0;
    let mut v___x_8297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8299_: u8 = 0;
    let mut v_isSharedCheck_8300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8271_ = l_Lean_realizeGlobalName(v_id_8267_, v_a_8268_, v_a_8269_);
                if lean_obj_tag(v___x_8271_) == 0 {
                    v_a_8272_ = lean_ctor_get(v___x_8271_, 0);
                    v_isSharedCheck_8300_ = (!lean_is_exclusive(v___x_8271_)) as u8;
                    if v_isSharedCheck_8300_ == 0 {
                        v___x_8274_ = v___x_8271_;
                        v_isShared_8275_ = v_isSharedCheck_8300_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8272_);
                        lean_dec(v___x_8271_);
                        v___x_8274_ = lean_box(0);
                        v_isShared_8275_ = v_isSharedCheck_8300_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_ref_8266_);
                    return v___x_8271_;
                }
            }
            1 => {
                v___x_8276_ = lean_st_ref_get(v_a_8269_);
                v_infoState_8277_ = lean_ctor_get(v___x_8276_, 7);
                lean_inc_ref(v_infoState_8277_);
                lean_dec(v___x_8276_);
                v_enabled_8278_ = lean_ctor_get_uint8(
                    v_infoState_8277_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_8277_);
                if v_enabled_8278_ == 0 {
                    lean_dec(v_ref_8266_);
                    if v_isShared_8275_ == 0 {
                        v___x_8280_ = v___x_8274_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8281_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8281_, 0, v_a_8272_);
                        v___x_8280_ = v_reuseFailAlloc_8281_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8274_);
                    v___x_8282_ = lean_box(0);
                    v___x_8283_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_8266_, v_a_8272_, v___x_8282_, v_a_8268_, v_a_8269_);
                    if lean_obj_tag(v___x_8283_) == 0 {
                        v_isSharedCheck_8290_ = (!lean_is_exclusive(v___x_8283_)) as u8;
                        if v_isSharedCheck_8290_ == 0 {
                            v_unused_8291_ = lean_ctor_get(v___x_8283_, 0);
                            lean_dec(v_unused_8291_);
                            v___x_8285_ = v___x_8283_;
                            v_isShared_8286_ = v_isSharedCheck_8290_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_8283_);
                            v___x_8285_ = lean_box(0);
                            v_isShared_8286_ = v_isSharedCheck_8290_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8272_);
                        v_a_8292_ = lean_ctor_get(v___x_8283_, 0);
                        v_isSharedCheck_8299_ = (!lean_is_exclusive(v___x_8283_)) as u8;
                        if v_isSharedCheck_8299_ == 0 {
                            v___x_8294_ = v___x_8283_;
                            v_isShared_8295_ = v_isSharedCheck_8299_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_8292_);
                            lean_dec(v___x_8283_);
                            v___x_8294_ = lean_box(0);
                            v_isShared_8295_ = v_isSharedCheck_8299_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8280_;
            }
            3 => {
                if v_isShared_8286_ == 0 {
                    lean_ctor_set(v___x_8285_, 0, v_a_8272_);
                    v___x_8288_ = v___x_8285_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8289_, 0, v_a_8272_);
                    v___x_8288_ = v_reuseFailAlloc_8289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8288_;
            }
            5 => {
                if v_isShared_8295_ == 0 {
                    v___x_8297_ = v___x_8294_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8298_, 0, v_a_8292_);
                    v___x_8297_ = v_reuseFailAlloc_8298_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_realizeGlobalNameWithInfos___boxed(
    mut v_ref_8301_: *mut LeanObject,
    mut v_id_8302_: *mut LeanObject,
    mut v_a_8303_: *mut LeanObject,
    mut v_a_8304_: *mut LeanObject,
    mut v_a_8305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8306_: *mut LeanObject = core::ptr::null_mut();
    v_res_8306_ =
        l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_8301_, v_id_8302_, v_a_8303_, v_a_8304_);
    lean_dec(v_a_8304_);
    lean_dec_ref(v_a_8303_);
    return v_res_8306_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(
    mut v_ref_8307_: *mut LeanObject,
    mut v_as_8308_: *mut LeanObject,
    mut v_as_x27_8309_: *mut LeanObject,
    mut v_b_8310_: *mut LeanObject,
    mut v_a_8311_: *mut LeanObject,
    mut v___y_8312_: *mut LeanObject,
    mut v___y_8313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8315_: *mut LeanObject = core::ptr::null_mut();
    v___x_8315_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(
            v_ref_8307_,
            v_as_x27_8309_,
            v_b_8310_,
            v___y_8312_,
            v___y_8313_,
        );
    return v___x_8315_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(
    mut v_ref_8316_: *mut LeanObject,
    mut v_as_8317_: *mut LeanObject,
    mut v_as_x27_8318_: *mut LeanObject,
    mut v_b_8319_: *mut LeanObject,
    mut v_a_8320_: *mut LeanObject,
    mut v___y_8321_: *mut LeanObject,
    mut v___y_8322_: *mut LeanObject,
    mut v___y_8323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8324_: *mut LeanObject = core::ptr::null_mut();
    v_res_8324_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(
        v_ref_8316_,
        v_as_8317_,
        v_as_x27_8318_,
        v_b_8319_,
        v_a_8320_,
        v___y_8321_,
        v___y_8322_,
    );
    lean_dec(v___y_8322_);
    lean_dec_ref(v___y_8321_);
    lean_dec(v_as_x27_8318_);
    lean_dec(v_as_8317_);
    return v_res_8324_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__0(
    mut v_self_8325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_8326_: *mut LeanObject = core::ptr::null_mut();
    v_fst_8326_ = lean_ctor_get(v_self_8325_, 0);
    lean_inc(v_fst_8326_);
    return v_fst_8326_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(
    mut v_self_8327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8328_: *mut LeanObject = core::ptr::null_mut();
    v_res_8328_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_8327_);
    lean_dec_ref(v_self_8327_);
    return v_res_8328_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__1(
    mut v_info_8329_: *mut LeanObject,
    mut v_treesSaved_8330_: *mut LeanObject,
    mut v_s_8331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_8332_: u8 = 0;
    let mut v_assignment_8333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_8335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8338_: u8 = 0;
    let mut v_val_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8345_: u8 = 0;
    let mut v_enabled_8346_: u8 = 0;
    let mut v_assignment_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8351_: u8 = 0;
    let mut v_val_8352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8355_: u8 = 0;
    let mut v___x_8357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8363_: u8 = 0;
    let mut v_isSharedCheck_8364_: u8 = 0;
    let mut v_unused_8365_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_8329_) == 0 {
                    v_enabled_8332_ = lean_ctor_get_uint8(
                        v_s_8331_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_assignment_8333_ = lean_ctor_get(v_s_8331_, 0);
                    v_lazyAssignment_8334_ = lean_ctor_get(v_s_8331_, 1);
                    v_trees_8335_ = lean_ctor_get(v_s_8331_, 2);
                    v_isSharedCheck_8345_ = (!lean_is_exclusive(v_s_8331_)) as u8;
                    if v_isSharedCheck_8345_ == 0 {
                        v___x_8337_ = v_s_8331_;
                        v_isShared_8338_ = v_isSharedCheck_8345_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_trees_8335_);
                        lean_inc(v_lazyAssignment_8334_);
                        lean_inc(v_assignment_8333_);
                        lean_dec(v_s_8331_);
                        v___x_8337_ = lean_box(0);
                        v_isShared_8338_ = v_isSharedCheck_8345_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_enabled_8346_ = lean_ctor_get_uint8(
                        v_s_8331_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_assignment_8347_ = lean_ctor_get(v_s_8331_, 0);
                    v_lazyAssignment_8348_ = lean_ctor_get(v_s_8331_, 1);
                    v_isSharedCheck_8364_ = (!lean_is_exclusive(v_s_8331_)) as u8;
                    if v_isSharedCheck_8364_ == 0 {
                        v_unused_8365_ = lean_ctor_get(v_s_8331_, 2);
                        lean_dec(v_unused_8365_);
                        v___x_8350_ = v_s_8331_;
                        v_isShared_8351_ = v_isSharedCheck_8364_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_lazyAssignment_8348_);
                        lean_inc(v_assignment_8347_);
                        lean_dec(v_s_8331_);
                        v___x_8350_ = lean_box(0);
                        v_isShared_8351_ = v_isSharedCheck_8364_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_val_8339_ = lean_ctor_get(v_info_8329_, 0);
                lean_inc(v_val_8339_);
                lean_dec_ref_known(v_info_8329_, 1);
                v___x_8340_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_8340_, 0, v_val_8339_);
                lean_ctor_set(v___x_8340_, 1, v_trees_8335_);
                v___x_8341_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_8330_, v___x_8340_);
                if v_isShared_8338_ == 0 {
                    lean_ctor_set(v___x_8337_, 2, v___x_8341_);
                    v___x_8343_ = v___x_8337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8344_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8344_, 0, v_assignment_8333_);
                    lean_ctor_set(v_reuseFailAlloc_8344_, 1, v_lazyAssignment_8334_);
                    lean_ctor_set(v_reuseFailAlloc_8344_, 2, v___x_8341_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8344_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_8332_,
                    );
                    v___x_8343_ = v_reuseFailAlloc_8344_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8343_;
            }
            3 => {
                v_val_8352_ = lean_ctor_get(v_info_8329_, 0);
                v_isSharedCheck_8363_ = (!lean_is_exclusive(v_info_8329_)) as u8;
                if v_isSharedCheck_8363_ == 0 {
                    v___x_8354_ = v_info_8329_;
                    v_isShared_8355_ = v_isSharedCheck_8363_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_val_8352_);
                    lean_dec(v_info_8329_);
                    v___x_8354_ = lean_box(0);
                    v_isShared_8355_ = v_isSharedCheck_8363_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_8355_ == 0 {
                    lean_ctor_set_tag(v___x_8354_, 2);
                    v___x_8357_ = v___x_8354_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8362_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8362_, 0, v_val_8352_);
                    v___x_8357_ = v_reuseFailAlloc_8362_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_8358_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_8330_, v___x_8357_);
                if v_isShared_8351_ == 0 {
                    lean_ctor_set(v___x_8350_, 2, v___x_8358_);
                    v___x_8360_ = v___x_8350_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8361_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8361_, 0, v_assignment_8347_);
                    lean_ctor_set(v_reuseFailAlloc_8361_, 1, v_lazyAssignment_8348_);
                    lean_ctor_set(v_reuseFailAlloc_8361_, 2, v___x_8358_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8361_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_8346_,
                    );
                    v___x_8360_ = v_reuseFailAlloc_8361_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__2(
    mut v_treesSaved_8366_: *mut LeanObject,
    mut v_modifyInfoState_8367_: *mut LeanObject,
    mut v_info_8368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8370_: *mut LeanObject = core::ptr::null_mut();
    v___f_8369_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8369_, 0, v_info_8368_);
    lean_closure_set(v___f_8369_, 1, v_treesSaved_8366_);
    v___x_8370_ = lean_apply_1(v_modifyInfoState_8367_, v___f_8369_);
    return v___x_8370_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__3(
    mut v___f_8371_: *mut LeanObject,
    mut v_info_8372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8373_: *mut LeanObject = core::ptr::null_mut();
    v___x_8373_ = lean_apply_1(v___f_8371_, v_info_8372_);
    return v___x_8373_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__4(
    mut v_toPure_8374_: *mut LeanObject,
    mut v_toBind_8375_: *mut LeanObject,
    mut v___f_8376_: *mut LeanObject,
    mut v_____do__lift_8377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8380_: *mut LeanObject = core::ptr::null_mut();
    v___x_8378_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8378_, 0, v_____do__lift_8377_);
    v___x_8379_ = lean_apply_2(v_toPure_8374_, lean_box(0), v___x_8378_);
    v___x_8380_ = lean_apply_4(
        v_toBind_8375_,
        lean_box(0),
        lean_box(0),
        v___x_8379_,
        v___f_8376_,
    );
    return v___x_8380_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__6(
    mut v_toBind_8381_: *mut LeanObject,
    mut v_mkInfoOnError_8382_: *mut LeanObject,
    mut v___f_8383_: *mut LeanObject,
    mut v_mkInfo_8384_: *mut LeanObject,
    mut v___f_8385_: *mut LeanObject,
    mut v_a_x3f_8386_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_x3f_8386_) == 0 {
        let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_8385_);
        lean_dec(v_mkInfo_8384_);
        v___x_8387_ = lean_apply_4(
            v_toBind_8381_,
            lean_box(0),
            lean_box(0),
            v_mkInfoOnError_8382_,
            v___f_8383_,
        );
        return v___x_8387_;
    } else {
        let mut v_val_8388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8390_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_8383_);
        lean_dec(v_mkInfoOnError_8382_);
        v_val_8388_ = lean_ctor_get(v_a_x3f_8386_, 0);
        lean_inc(v_val_8388_);
        lean_dec_ref_known(v_a_x3f_8386_, 1);
        v___x_8389_ = lean_apply_1(v_mkInfo_8384_, v_val_8388_);
        v___x_8390_ = lean_apply_4(
            v_toBind_8381_,
            lean_box(0),
            lean_box(0),
            v___x_8389_,
            v___f_8385_,
        );
        return v___x_8390_;
    }
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__5(
    mut v_toApplicative_8391_: *mut LeanObject,
    mut v_modifyInfoState_8392_: *mut LeanObject,
    mut v_toBind_8393_: *mut LeanObject,
    mut v_mkInfoOnError_8394_: *mut LeanObject,
    mut v_mkInfo_8395_: *mut LeanObject,
    mut v_inst_8396_: *mut LeanObject,
    mut v_x_8397_: *mut LeanObject,
    mut v___f_8398_: *mut LeanObject,
    mut v_treesSaved_8399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toFunctor_8400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_8402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8408_: *mut LeanObject = core::ptr::null_mut();
    v_toFunctor_8400_ = lean_ctor_get(v_toApplicative_8391_, 0);
    lean_inc_ref(v_toFunctor_8400_);
    v_toPure_8401_ = lean_ctor_get(v_toApplicative_8391_, 1);
    lean_inc(v_toPure_8401_);
    lean_dec_ref(v_toApplicative_8391_);
    v_map_8402_ = lean_ctor_get(v_toFunctor_8400_, 0);
    lean_inc(v_map_8402_);
    lean_dec_ref(v_toFunctor_8400_);
    v___f_8403_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8403_, 0, v_treesSaved_8399_);
    lean_closure_set(v___f_8403_, 1, v_modifyInfoState_8392_);
    v___f_8404_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8404_, 0, v___f_8403_);
    lean_inc_ref(v___f_8404_);
    lean_inc(v_toBind_8393_);
    v___f_8405_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8405_, 0, v_toPure_8401_);
    lean_closure_set(v___f_8405_, 1, v_toBind_8393_);
    lean_closure_set(v___f_8405_, 2, v___f_8404_);
    v___f_8406_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__6 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_8406_, 0, v_toBind_8393_);
    lean_closure_set(v___f_8406_, 1, v_mkInfoOnError_8394_);
    lean_closure_set(v___f_8406_, 2, v___f_8405_);
    lean_closure_set(v___f_8406_, 3, v_mkInfo_8395_);
    lean_closure_set(v___f_8406_, 4, v___f_8404_);
    v___x_8407_ = lean_apply_4(
        v_inst_8396_,
        lean_box(0),
        lean_box(0),
        v_x_8397_,
        v___f_8406_,
    );
    v___x_8408_ = lean_apply_4(
        v_map_8402_,
        lean_box(0),
        lean_box(0),
        v___f_8398_,
        v___x_8407_,
    );
    return v___x_8408_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__7(
    mut v_x_8409_: *mut LeanObject,
    mut v_inst_8410_: *mut LeanObject,
    mut v_inst_8411_: *mut LeanObject,
    mut v_toBind_8412_: *mut LeanObject,
    mut v___f_8413_: *mut LeanObject,
    mut v_____do__lift_8414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_8415_: u8 = 0;
    v_enabled_8415_ = lean_ctor_get_uint8(
        v_____do__lift_8414_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    if v_enabled_8415_ == 0 {
        lean_dec(v___f_8413_);
        lean_dec(v_toBind_8412_);
        lean_dec_ref(v_inst_8411_);
        lean_dec_ref(v_inst_8410_);
        lean_inc(v_x_8409_);
        return v_x_8409_;
    } else {
        let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8417_: *mut LeanObject = core::ptr::null_mut();
        v___x_8416_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_8410_, v_inst_8411_);
        v___x_8417_ = lean_apply_4(
            v_toBind_8412_,
            lean_box(0),
            lean_box(0),
            v___x_8416_,
            v___f_8413_,
        );
        return v___x_8417_;
    }
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(
    mut v_x_8418_: *mut LeanObject,
    mut v_inst_8419_: *mut LeanObject,
    mut v_inst_8420_: *mut LeanObject,
    mut v_toBind_8421_: *mut LeanObject,
    mut v___f_8422_: *mut LeanObject,
    mut v_____do__lift_8423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8424_: *mut LeanObject = core::ptr::null_mut();
    v_res_8424_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(
        v_x_8418_,
        v_inst_8419_,
        v_inst_8420_,
        v_toBind_8421_,
        v___f_8422_,
        v_____do__lift_8423_,
    );
    lean_dec_ref(v_____do__lift_8423_);
    lean_dec(v_x_8418_);
    return v_res_8424_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___redArg(
    mut v_inst_8426_: *mut LeanObject,
    mut v_inst_8427_: *mut LeanObject,
    mut v_inst_8428_: *mut LeanObject,
    mut v_x_8429_: *mut LeanObject,
    mut v_mkInfo_8430_: *mut LeanObject,
    mut v_mkInfoOnError_8431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_8434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_8435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8439_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8432_ = lean_ctor_get(v_inst_8426_, 0);
    v_toBind_8433_ = lean_ctor_get(v_inst_8426_, 1);
    lean_inc_n(v_toBind_8433_, 3);
    v_getInfoState_8434_ = lean_ctor_get(v_inst_8427_, 0);
    lean_inc(v_getInfoState_8434_);
    v_modifyInfoState_8435_ = lean_ctor_get(v_inst_8427_, 1);
    v___f_8436_ = l_Lean_Elab_withInfoContext_x27___redArg___closed__0;
    lean_inc(v_x_8429_);
    lean_inc(v_modifyInfoState_8435_);
    lean_inc_ref(v_toApplicative_8432_);
    v___f_8437_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__5 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_8437_, 0, v_toApplicative_8432_);
    lean_closure_set(v___f_8437_, 1, v_modifyInfoState_8435_);
    lean_closure_set(v___f_8437_, 2, v_toBind_8433_);
    lean_closure_set(v___f_8437_, 3, v_mkInfoOnError_8431_);
    lean_closure_set(v___f_8437_, 4, v_mkInfo_8430_);
    lean_closure_set(v___f_8437_, 5, v_inst_8428_);
    lean_closure_set(v___f_8437_, 6, v_x_8429_);
    lean_closure_set(v___f_8437_, 7, v___f_8436_);
    v___f_8438_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_8438_, 0, v_x_8429_);
    lean_closure_set(v___f_8438_, 1, v_inst_8426_);
    lean_closure_set(v___f_8438_, 2, v_inst_8427_);
    lean_closure_set(v___f_8438_, 3, v_toBind_8433_);
    lean_closure_set(v___f_8438_, 4, v___f_8437_);
    v___x_8439_ = lean_apply_4(
        v_toBind_8433_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_8434_,
        v___f_8438_,
    );
    return v___x_8439_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27(
    mut v_m_8440_: *mut LeanObject,
    mut v_inst_8441_: *mut LeanObject,
    mut v_inst_8442_: *mut LeanObject,
    mut v_00_u03b1_8443_: *mut LeanObject,
    mut v_inst_8444_: *mut LeanObject,
    mut v_x_8445_: *mut LeanObject,
    mut v_mkInfo_8446_: *mut LeanObject,
    mut v_mkInfoOnError_8447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8448_: *mut LeanObject = core::ptr::null_mut();
    v___x_8448_ = l_Lean_Elab_withInfoContext_x27___redArg(
        v_inst_8441_,
        v_inst_8442_,
        v_inst_8444_,
        v_x_8445_,
        v_mkInfo_8446_,
        v_mkInfoOnError_8447_,
    );
    return v___x_8448_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___redArg___lam__1(
    mut v_treesSaved_8449_: *mut LeanObject,
    mut v_tree_8450_: *mut LeanObject,
    mut v_s_8451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_8452_: u8 = 0;
    let mut v_assignment_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8457_: u8 = 0;
    let mut v___x_8458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8462_: u8 = 0;
    let mut v_unused_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_enabled_8452_ = lean_ctor_get_uint8(
                    v_s_8451_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_8453_ = lean_ctor_get(v_s_8451_, 0);
                v_lazyAssignment_8454_ = lean_ctor_get(v_s_8451_, 1);
                v_isSharedCheck_8462_ = (!lean_is_exclusive(v_s_8451_)) as u8;
                if v_isSharedCheck_8462_ == 0 {
                    v_unused_8463_ = lean_ctor_get(v_s_8451_, 2);
                    lean_dec(v_unused_8463_);
                    v___x_8456_ = v_s_8451_;
                    v_isShared_8457_ = v_isSharedCheck_8462_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_8454_);
                    lean_inc(v_assignment_8453_);
                    lean_dec(v_s_8451_);
                    v___x_8456_ = lean_box(0);
                    v_isShared_8457_ = v_isSharedCheck_8462_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8458_ =
                    l_Lean_PersistentArray_push___redArg(v_treesSaved_8449_, v_tree_8450_);
                if v_isShared_8457_ == 0 {
                    lean_ctor_set(v___x_8456_, 2, v___x_8458_);
                    v___x_8460_ = v___x_8456_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8461_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8461_, 0, v_assignment_8453_);
                    lean_ctor_set(v_reuseFailAlloc_8461_, 1, v_lazyAssignment_8454_);
                    lean_ctor_set(v_reuseFailAlloc_8461_, 2, v___x_8458_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8461_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_8452_,
                    );
                    v___x_8460_ = v_reuseFailAlloc_8461_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___redArg___lam__0(
    mut v_treesSaved_8464_: *mut LeanObject,
    mut v_modifyInfoState_8465_: *mut LeanObject,
    mut v_tree_8466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8468_: *mut LeanObject = core::ptr::null_mut();
    v___f_8467_ = lean_alloc_closure(
        l_Lean_Elab_withInfoTreeContext___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8467_, 0, v_treesSaved_8464_);
    lean_closure_set(v___f_8467_, 1, v_tree_8466_);
    v___x_8468_ = lean_apply_1(v_modifyInfoState_8465_, v___f_8467_);
    return v___x_8468_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___redArg___lam__2(
    mut v_mkInfoTree_8469_: *mut LeanObject,
    mut v_toBind_8470_: *mut LeanObject,
    mut v___f_8471_: *mut LeanObject,
    mut v_st_8472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_trees_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8475_: *mut LeanObject = core::ptr::null_mut();
    v_trees_8473_ = lean_ctor_get(v_st_8472_, 2);
    lean_inc_ref(v_trees_8473_);
    lean_dec_ref(v_st_8472_);
    v___x_8474_ = lean_apply_1(v_mkInfoTree_8469_, v_trees_8473_);
    v___x_8475_ = lean_apply_4(
        v_toBind_8470_,
        lean_box(0),
        lean_box(0),
        v___x_8474_,
        v___f_8471_,
    );
    return v___x_8475_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___redArg___lam__3(
    mut v_toBind_8476_: *mut LeanObject,
    mut v_getInfoState_8477_: *mut LeanObject,
    mut v___f_8478_: *mut LeanObject,
    mut v_x_8479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8480_: *mut LeanObject = core::ptr::null_mut();
    v___x_8480_ = lean_apply_4(
        v_toBind_8476_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_8477_,
        v___f_8478_,
    );
    return v___x_8480_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(
    mut v_toBind_8481_: *mut LeanObject,
    mut v_getInfoState_8482_: *mut LeanObject,
    mut v___f_8483_: *mut LeanObject,
    mut v_x_8484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8485_: *mut LeanObject = core::ptr::null_mut();
    v_res_8485_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(
        v_toBind_8481_,
        v_getInfoState_8482_,
        v___f_8483_,
        v_x_8484_,
    );
    lean_dec(v_x_8484_);
    return v_res_8485_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___redArg___lam__4(
    mut v_toApplicative_8486_: *mut LeanObject,
    mut v_modifyInfoState_8487_: *mut LeanObject,
    mut v_mkInfoTree_8488_: *mut LeanObject,
    mut v_toBind_8489_: *mut LeanObject,
    mut v_getInfoState_8490_: *mut LeanObject,
    mut v_inst_8491_: *mut LeanObject,
    mut v_x_8492_: *mut LeanObject,
    mut v___f_8493_: *mut LeanObject,
    mut v_treesSaved_8494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toFunctor_8495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_8496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8501_: *mut LeanObject = core::ptr::null_mut();
    v_toFunctor_8495_ = lean_ctor_get(v_toApplicative_8486_, 0);
    lean_inc_ref(v_toFunctor_8495_);
    lean_dec_ref(v_toApplicative_8486_);
    v_map_8496_ = lean_ctor_get(v_toFunctor_8495_, 0);
    lean_inc(v_map_8496_);
    lean_dec_ref(v_toFunctor_8495_);
    v___f_8497_ = lean_alloc_closure(
        l_Lean_Elab_withInfoTreeContext___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8497_, 0, v_treesSaved_8494_);
    lean_closure_set(v___f_8497_, 1, v_modifyInfoState_8487_);
    lean_inc(v_toBind_8489_);
    v___f_8498_ = lean_alloc_closure(
        l_Lean_Elab_withInfoTreeContext___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8498_, 0, v_mkInfoTree_8488_);
    lean_closure_set(v___f_8498_, 1, v_toBind_8489_);
    lean_closure_set(v___f_8498_, 2, v___f_8497_);
    v___f_8499_ = lean_alloc_closure(
        l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8499_, 0, v_toBind_8489_);
    lean_closure_set(v___f_8499_, 1, v_getInfoState_8490_);
    lean_closure_set(v___f_8499_, 2, v___f_8498_);
    v___x_8500_ = lean_apply_4(
        v_inst_8491_,
        lean_box(0),
        lean_box(0),
        v_x_8492_,
        v___f_8499_,
    );
    v___x_8501_ = lean_apply_4(
        v_map_8496_,
        lean_box(0),
        lean_box(0),
        v___f_8493_,
        v___x_8500_,
    );
    return v___x_8501_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___redArg(
    mut v_inst_8502_: *mut LeanObject,
    mut v_inst_8503_: *mut LeanObject,
    mut v_inst_8504_: *mut LeanObject,
    mut v_x_8505_: *mut LeanObject,
    mut v_mkInfoTree_8506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_8509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_8510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8514_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8507_ = lean_ctor_get(v_inst_8502_, 0);
    v_toBind_8508_ = lean_ctor_get(v_inst_8502_, 1);
    lean_inc_n(v_toBind_8508_, 3);
    v_getInfoState_8509_ = lean_ctor_get(v_inst_8503_, 0);
    lean_inc_n(v_getInfoState_8509_, 2);
    v_modifyInfoState_8510_ = lean_ctor_get(v_inst_8503_, 1);
    v___f_8511_ = l_Lean_Elab_withInfoContext_x27___redArg___closed__0;
    lean_inc(v_x_8505_);
    lean_inc(v_modifyInfoState_8510_);
    lean_inc_ref(v_toApplicative_8507_);
    v___f_8512_ = lean_alloc_closure(
        l_Lean_Elab_withInfoTreeContext___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_8512_, 0, v_toApplicative_8507_);
    lean_closure_set(v___f_8512_, 1, v_modifyInfoState_8510_);
    lean_closure_set(v___f_8512_, 2, v_mkInfoTree_8506_);
    lean_closure_set(v___f_8512_, 3, v_toBind_8508_);
    lean_closure_set(v___f_8512_, 4, v_getInfoState_8509_);
    lean_closure_set(v___f_8512_, 5, v_inst_8504_);
    lean_closure_set(v___f_8512_, 6, v_x_8505_);
    lean_closure_set(v___f_8512_, 7, v___f_8511_);
    v___f_8513_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_8513_, 0, v_x_8505_);
    lean_closure_set(v___f_8513_, 1, v_inst_8502_);
    lean_closure_set(v___f_8513_, 2, v_inst_8503_);
    lean_closure_set(v___f_8513_, 3, v_toBind_8508_);
    lean_closure_set(v___f_8513_, 4, v___f_8512_);
    v___x_8514_ = lean_apply_4(
        v_toBind_8508_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_8509_,
        v___f_8513_,
    );
    return v___x_8514_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext(
    mut v_m_8515_: *mut LeanObject,
    mut v_inst_8516_: *mut LeanObject,
    mut v_inst_8517_: *mut LeanObject,
    mut v_00_u03b1_8518_: *mut LeanObject,
    mut v_inst_8519_: *mut LeanObject,
    mut v_x_8520_: *mut LeanObject,
    mut v_mkInfoTree_8521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8522_: *mut LeanObject = core::ptr::null_mut();
    v___x_8522_ = l_Lean_Elab_withInfoTreeContext___redArg(
        v_inst_8516_,
        v_inst_8517_,
        v_inst_8519_,
        v_x_8520_,
        v_mkInfoTree_8521_,
    );
    return v___x_8522_;
}
pub unsafe fn l_Lean_Elab_withInfoContext___redArg___lam__0(
    mut v_trees_8523_: *mut LeanObject,
    mut v_toPure_8524_: *mut LeanObject,
    mut v_____do__lift_8525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8527_: *mut LeanObject = core::ptr::null_mut();
    v___x_8526_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8526_, 0, v_____do__lift_8525_);
    lean_ctor_set(v___x_8526_, 1, v_trees_8523_);
    v___x_8527_ = lean_apply_2(v_toPure_8524_, lean_box(0), v___x_8526_);
    return v___x_8527_;
}
pub unsafe fn l_Lean_Elab_withInfoContext___redArg___lam__1(
    mut v_toPure_8528_: *mut LeanObject,
    mut v_toBind_8529_: *mut LeanObject,
    mut v_mkInfo_8530_: *mut LeanObject,
    mut v_trees_8531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8533_: *mut LeanObject = core::ptr::null_mut();
    v___f_8532_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8532_, 0, v_trees_8531_);
    lean_closure_set(v___f_8532_, 1, v_toPure_8528_);
    v___x_8533_ = lean_apply_4(
        v_toBind_8529_,
        lean_box(0),
        lean_box(0),
        v_mkInfo_8530_,
        v___f_8532_,
    );
    return v___x_8533_;
}
pub unsafe fn l_Lean_Elab_withInfoContext___redArg(
    mut v_inst_8534_: *mut LeanObject,
    mut v_inst_8535_: *mut LeanObject,
    mut v_inst_8536_: *mut LeanObject,
    mut v_x_8537_: *mut LeanObject,
    mut v_mkInfo_8538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8543_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8539_ = lean_ctor_get(v_inst_8534_, 0);
    v_toBind_8540_ = lean_ctor_get(v_inst_8534_, 1);
    v_toPure_8541_ = lean_ctor_get(v_toApplicative_8539_, 1);
    lean_inc(v_toBind_8540_);
    lean_inc(v_toPure_8541_);
    v___f_8542_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8542_, 0, v_toPure_8541_);
    lean_closure_set(v___f_8542_, 1, v_toBind_8540_);
    lean_closure_set(v___f_8542_, 2, v_mkInfo_8538_);
    v___x_8543_ = l_Lean_Elab_withInfoTreeContext___redArg(
        v_inst_8534_,
        v_inst_8535_,
        v_inst_8536_,
        v_x_8537_,
        v___f_8542_,
    );
    return v___x_8543_;
}
pub unsafe fn l_Lean_Elab_withInfoContext(
    mut v_m_8544_: *mut LeanObject,
    mut v_inst_8545_: *mut LeanObject,
    mut v_inst_8546_: *mut LeanObject,
    mut v_00_u03b1_8547_: *mut LeanObject,
    mut v_inst_8548_: *mut LeanObject,
    mut v_x_8549_: *mut LeanObject,
    mut v_mkInfo_8550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8555_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8551_ = lean_ctor_get(v_inst_8545_, 0);
    v_toBind_8552_ = lean_ctor_get(v_inst_8545_, 1);
    v_toPure_8553_ = lean_ctor_get(v_toApplicative_8551_, 1);
    lean_inc(v_toBind_8552_);
    lean_inc(v_toPure_8553_);
    v___f_8554_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8554_, 0, v_toPure_8553_);
    lean_closure_set(v___f_8554_, 1, v_toBind_8552_);
    lean_closure_set(v___f_8554_, 2, v_mkInfo_8550_);
    v___x_8555_ = l_Lean_Elab_withInfoTreeContext___redArg(
        v_inst_8545_,
        v_inst_8546_,
        v_inst_8548_,
        v_x_8549_,
        v___f_8554_,
    );
    return v___x_8555_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(
    mut v_treesSaved_8556_: *mut LeanObject,
    mut v_trees_8557_: *mut LeanObject,
    mut v_s_8558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_8559_: u8 = 0;
    let mut v_assignment_8560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8564_: u8 = 0;
    let mut v___x_8565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8569_: u8 = 0;
    let mut v_unused_8570_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_enabled_8559_ = lean_ctor_get_uint8(
                    v_s_8558_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_8560_ = lean_ctor_get(v_s_8558_, 0);
                v_lazyAssignment_8561_ = lean_ctor_get(v_s_8558_, 1);
                v_isSharedCheck_8569_ = (!lean_is_exclusive(v_s_8558_)) as u8;
                if v_isSharedCheck_8569_ == 0 {
                    v_unused_8570_ = lean_ctor_get(v_s_8558_, 2);
                    lean_dec(v_unused_8570_);
                    v___x_8563_ = v_s_8558_;
                    v_isShared_8564_ = v_isSharedCheck_8569_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_8561_);
                    lean_inc(v_assignment_8560_);
                    lean_dec(v_s_8558_);
                    v___x_8563_ = lean_box(0);
                    v_isShared_8564_ = v_isSharedCheck_8569_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8565_ =
                    l_Lean_PersistentArray_append___redArg(v_treesSaved_8556_, v_trees_8557_);
                if v_isShared_8564_ == 0 {
                    lean_ctor_set(v___x_8563_, 2, v___x_8565_);
                    v___x_8567_ = v___x_8563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8568_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8568_, 0, v_assignment_8560_);
                    lean_ctor_set(v_reuseFailAlloc_8568_, 1, v_lazyAssignment_8561_);
                    lean_ctor_set(v_reuseFailAlloc_8568_, 2, v___x_8565_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8568_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_8559_,
                    );
                    v___x_8567_ = v_reuseFailAlloc_8568_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(
    mut v_treesSaved_8571_: *mut LeanObject,
    mut v_trees_8572_: *mut LeanObject,
    mut v_s_8573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8574_: *mut LeanObject = core::ptr::null_mut();
    v_res_8574_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_8571_, v_trees_8572_, v_s_8573_);
    lean_dec_ref(v_trees_8572_);
    return v_res_8574_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(
    mut v_treesSaved_8575_: *mut LeanObject,
    mut v_modifyInfoState_8576_: *mut LeanObject,
    mut v_trees_8577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8579_: *mut LeanObject = core::ptr::null_mut();
    v___f_8578_ = lean_alloc_closure(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___f_8578_, 0, v_treesSaved_8575_);
    lean_closure_set(v___f_8578_, 1, v_trees_8577_);
    v___x_8579_ = lean_apply_1(v_modifyInfoState_8576_, v___f_8578_);
    return v___x_8579_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(
    mut v_toPure_8580_: *mut LeanObject,
    mut v_tree_8581_: *mut LeanObject,
    mut v_____do__lift_8582_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_8582_) == 0 {
        let mut v___x_8583_: *mut LeanObject = core::ptr::null_mut();
        v___x_8583_ = lean_apply_2(v_toPure_8580_, lean_box(0), v_tree_8581_);
        return v___x_8583_;
    } else {
        let mut v_val_8584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8586_: *mut LeanObject = core::ptr::null_mut();
        v_val_8584_ = lean_ctor_get(v_____do__lift_8582_, 0);
        lean_inc(v_val_8584_);
        v___x_8585_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_8585_, 0, v_val_8584_);
        lean_ctor_set(v___x_8585_, 1, v_tree_8581_);
        v___x_8586_ = lean_apply_2(v_toPure_8580_, lean_box(0), v___x_8585_);
        return v___x_8586_;
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(
    mut v_toPure_8587_: *mut LeanObject,
    mut v_tree_8588_: *mut LeanObject,
    mut v_____do__lift_8589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8590_: *mut LeanObject = core::ptr::null_mut();
    v_res_8590_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_8587_, v_tree_8588_, v_____do__lift_8589_);
    lean_dec(v_____do__lift_8589_);
    return v_res_8590_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(
    mut v_assignment_8591_: *mut LeanObject,
    mut v_toPure_8592_: *mut LeanObject,
    mut v_toBind_8593_: *mut LeanObject,
    mut v_ctx_x3f_8594_: *mut LeanObject,
    mut v_tree_8595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tree_8596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8598_: *mut LeanObject = core::ptr::null_mut();
    v_tree_8596_ = l_Lean_Elab_InfoTree_substitute(v_tree_8595_, v_assignment_8591_);
    v___f_8597_ = lean_alloc_closure(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___f_8597_, 0, v_toPure_8592_);
    lean_closure_set(v___f_8597_, 1, v_tree_8596_);
    v___x_8598_ = lean_apply_4(
        v_toBind_8593_,
        lean_box(0),
        lean_box(0),
        v_ctx_x3f_8594_,
        v___f_8597_,
    );
    return v___x_8598_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(
    mut v_assignment_8599_: *mut LeanObject,
    mut v_toPure_8600_: *mut LeanObject,
    mut v_toBind_8601_: *mut LeanObject,
    mut v_ctx_x3f_8602_: *mut LeanObject,
    mut v_tree_8603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8604_: *mut LeanObject = core::ptr::null_mut();
    v_res_8604_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_8599_, v_toPure_8600_, v_toBind_8601_, v_ctx_x3f_8602_, v_tree_8603_);
    lean_dec_ref(v_assignment_8599_);
    return v_res_8604_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(
    mut v_toPure_8605_: *mut LeanObject,
    mut v_toBind_8606_: *mut LeanObject,
    mut v_ctx_x3f_8607_: *mut LeanObject,
    mut v_inst_8608_: *mut LeanObject,
    mut v___f_8609_: *mut LeanObject,
    mut v_st_8610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_assignment_8611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_8612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8615_: *mut LeanObject = core::ptr::null_mut();
    v_assignment_8611_ = lean_ctor_get(v_st_8610_, 0);
    lean_inc_ref(v_assignment_8611_);
    v_trees_8612_ = lean_ctor_get(v_st_8610_, 2);
    lean_inc_ref(v_trees_8612_);
    lean_dec_ref(v_st_8610_);
    lean_inc(v_toBind_8606_);
    v___f_8613_ = lean_alloc_closure(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___f_8613_, 0, v_assignment_8611_);
    lean_closure_set(v___f_8613_, 1, v_toPure_8605_);
    lean_closure_set(v___f_8613_, 2, v_toBind_8606_);
    lean_closure_set(v___f_8613_, 3, v_ctx_x3f_8607_);
    v___x_8614_ = l_Lean_PersistentArray_mapM___redArg(v_inst_8608_, v___f_8613_, v_trees_8612_);
    v___x_8615_ = lean_apply_4(
        v_toBind_8606_,
        lean_box(0),
        lean_box(0),
        v___x_8614_,
        v___f_8609_,
    );
    return v___x_8615_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(
    mut v_toApplicative_8616_: *mut LeanObject,
    mut v_modifyInfoState_8617_: *mut LeanObject,
    mut v_toBind_8618_: *mut LeanObject,
    mut v_ctx_x3f_8619_: *mut LeanObject,
    mut v_inst_8620_: *mut LeanObject,
    mut v_getInfoState_8621_: *mut LeanObject,
    mut v_inst_8622_: *mut LeanObject,
    mut v_x_8623_: *mut LeanObject,
    mut v___f_8624_: *mut LeanObject,
    mut v_treesSaved_8625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toFunctor_8626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_8628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8633_: *mut LeanObject = core::ptr::null_mut();
    v_toFunctor_8626_ = lean_ctor_get(v_toApplicative_8616_, 0);
    lean_inc_ref(v_toFunctor_8626_);
    v_toPure_8627_ = lean_ctor_get(v_toApplicative_8616_, 1);
    lean_inc(v_toPure_8627_);
    lean_dec_ref(v_toApplicative_8616_);
    v_map_8628_ = lean_ctor_get(v_toFunctor_8626_, 0);
    lean_inc(v_map_8628_);
    lean_dec_ref(v_toFunctor_8626_);
    v___f_8629_ = lean_alloc_closure(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___f_8629_, 0, v_treesSaved_8625_);
    lean_closure_set(v___f_8629_, 1, v_modifyInfoState_8617_);
    lean_inc(v_toBind_8618_);
    v___f_8630_ = lean_alloc_closure(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4 as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_8630_, 0, v_toPure_8627_);
    lean_closure_set(v___f_8630_, 1, v_toBind_8618_);
    lean_closure_set(v___f_8630_, 2, v_ctx_x3f_8619_);
    lean_closure_set(v___f_8630_, 3, v_inst_8620_);
    lean_closure_set(v___f_8630_, 4, v___f_8629_);
    v___f_8631_ = lean_alloc_closure(
        l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8631_, 0, v_toBind_8618_);
    lean_closure_set(v___f_8631_, 1, v_getInfoState_8621_);
    lean_closure_set(v___f_8631_, 2, v___f_8630_);
    v___x_8632_ = lean_apply_4(
        v_inst_8622_,
        lean_box(0),
        lean_box(0),
        v_x_8623_,
        v___f_8631_,
    );
    v___x_8633_ = lean_apply_4(
        v_map_8628_,
        lean_box(0),
        lean_box(0),
        v___f_8624_,
        v___x_8632_,
    );
    return v___x_8633_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(
    mut v_inst_8634_: *mut LeanObject,
    mut v_inst_8635_: *mut LeanObject,
    mut v_inst_8636_: *mut LeanObject,
    mut v_x_8637_: *mut LeanObject,
    mut v_ctx_x3f_8638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_8641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_8642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8646_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8639_ = lean_ctor_get(v_inst_8634_, 0);
    v_toBind_8640_ = lean_ctor_get(v_inst_8634_, 1);
    lean_inc_n(v_toBind_8640_, 3);
    v_getInfoState_8641_ = lean_ctor_get(v_inst_8635_, 0);
    lean_inc_n(v_getInfoState_8641_, 2);
    v_modifyInfoState_8642_ = lean_ctor_get(v_inst_8635_, 1);
    v___f_8643_ = l_Lean_Elab_withInfoContext_x27___redArg___closed__0;
    lean_inc(v_x_8637_);
    lean_inc_ref(v_inst_8634_);
    lean_inc(v_modifyInfoState_8642_);
    lean_inc_ref(v_toApplicative_8639_);
    v___f_8644_ = lean_alloc_closure(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6 as *mut core::ffi::c_void, 10, 9);
    lean_closure_set(v___f_8644_, 0, v_toApplicative_8639_);
    lean_closure_set(v___f_8644_, 1, v_modifyInfoState_8642_);
    lean_closure_set(v___f_8644_, 2, v_toBind_8640_);
    lean_closure_set(v___f_8644_, 3, v_ctx_x3f_8638_);
    lean_closure_set(v___f_8644_, 4, v_inst_8634_);
    lean_closure_set(v___f_8644_, 5, v_getInfoState_8641_);
    lean_closure_set(v___f_8644_, 6, v_inst_8636_);
    lean_closure_set(v___f_8644_, 7, v_x_8637_);
    lean_closure_set(v___f_8644_, 8, v___f_8643_);
    v___f_8645_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_8645_, 0, v_x_8637_);
    lean_closure_set(v___f_8645_, 1, v_inst_8634_);
    lean_closure_set(v___f_8645_, 2, v_inst_8635_);
    lean_closure_set(v___f_8645_, 3, v_toBind_8640_);
    lean_closure_set(v___f_8645_, 4, v___f_8644_);
    v___x_8646_ = lean_apply_4(
        v_toBind_8640_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_8641_,
        v___f_8645_,
    );
    return v___x_8646_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(
    mut v_m_8647_: *mut LeanObject,
    mut v_inst_8648_: *mut LeanObject,
    mut v_inst_8649_: *mut LeanObject,
    mut v_00_u03b1_8650_: *mut LeanObject,
    mut v_inst_8651_: *mut LeanObject,
    mut v_x_8652_: *mut LeanObject,
    mut v_ctx_x3f_8653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8654_: *mut LeanObject = core::ptr::null_mut();
    v___x_8654_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(
            v_inst_8648_,
            v_inst_8649_,
            v_inst_8651_,
            v_x_8652_,
            v_ctx_x3f_8653_,
        );
    return v___x_8654_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___redArg___lam__0(
    mut v_toPure_8655_: *mut LeanObject,
    mut v_____do__lift_8656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8659_: *mut LeanObject = core::ptr::null_mut();
    v___x_8657_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8657_, 0, v_____do__lift_8656_);
    v___x_8658_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8658_, 0, v___x_8657_);
    v___x_8659_ = lean_apply_2(v_toPure_8655_, lean_box(0), v___x_8658_);
    return v___x_8659_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___redArg(
    mut v_inst_8660_: *mut LeanObject,
    mut v_inst_8661_: *mut LeanObject,
    mut v_inst_8662_: *mut LeanObject,
    mut v_inst_8663_: *mut LeanObject,
    mut v_inst_8664_: *mut LeanObject,
    mut v_inst_8665_: *mut LeanObject,
    mut v_inst_8666_: *mut LeanObject,
    mut v_inst_8667_: *mut LeanObject,
    mut v_inst_8668_: *mut LeanObject,
    mut v_x_8669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8676_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8670_ = lean_ctor_get(v_inst_8660_, 0);
    v_toBind_8671_ = lean_ctor_get(v_inst_8660_, 1);
    v_toPure_8672_ = lean_ctor_get(v_toApplicative_8670_, 1);
    lean_inc_ref(v_inst_8660_);
    v___x_8673_ = l_Lean_Elab_CommandContextInfo_save___redArg(
        v_inst_8660_,
        v_inst_8664_,
        v_inst_8666_,
        v_inst_8665_,
        v_inst_8667_,
        v_inst_8662_,
        v_inst_8668_,
    );
    lean_inc(v_toPure_8672_);
    v___f_8674_ = lean_alloc_closure(
        l_Lean_Elab_withSaveInfoContext___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8674_, 0, v_toPure_8672_);
    lean_inc(v_toBind_8671_);
    v___x_8675_ = lean_apply_4(
        v_toBind_8671_,
        lean_box(0),
        lean_box(0),
        v___x_8673_,
        v___f_8674_,
    );
    v___x_8676_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(
            v_inst_8660_,
            v_inst_8661_,
            v_inst_8663_,
            v_x_8669_,
            v___x_8675_,
        );
    return v___x_8676_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext(
    mut v_m_8677_: *mut LeanObject,
    mut v_inst_8678_: *mut LeanObject,
    mut v_inst_8679_: *mut LeanObject,
    mut v_00_u03b1_8680_: *mut LeanObject,
    mut v_inst_8681_: *mut LeanObject,
    mut v_inst_8682_: *mut LeanObject,
    mut v_inst_8683_: *mut LeanObject,
    mut v_inst_8684_: *mut LeanObject,
    mut v_inst_8685_: *mut LeanObject,
    mut v_inst_8686_: *mut LeanObject,
    mut v_inst_8687_: *mut LeanObject,
    mut v_x_8688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8689_: *mut LeanObject = core::ptr::null_mut();
    v___x_8689_ = l_Lean_Elab_withSaveInfoContext___redArg(
        v_inst_8678_,
        v_inst_8679_,
        v_inst_8681_,
        v_inst_8682_,
        v_inst_8683_,
        v_inst_8684_,
        v_inst_8685_,
        v_inst_8686_,
        v_inst_8687_,
        v_x_8688_,
    );
    return v___x_8689_;
}
pub unsafe fn l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(
    mut v_toPure_8690_: *mut LeanObject,
    mut v_____x_8691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_8692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8695_: u8 = 0;
    let mut v___x_8696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8701_: u8 = 0;
    let mut v___x_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8703_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____x_8691_) == 1 {
                    v_val_8692_ = lean_ctor_get(v_____x_8691_, 0);
                    v_isSharedCheck_8701_ = (!lean_is_exclusive(v_____x_8691_)) as u8;
                    if v_isSharedCheck_8701_ == 0 {
                        v___x_8694_ = v_____x_8691_;
                        v_isShared_8695_ = v_isSharedCheck_8701_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_8692_);
                        lean_dec(v_____x_8691_);
                        v___x_8694_ = lean_box(0);
                        v_isShared_8695_ = v_isSharedCheck_8701_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_____x_8691_);
                    v___x_8702_ = lean_box(0);
                    v___x_8703_ = lean_apply_2(v_toPure_8690_, lean_box(0), v___x_8702_);
                    return v___x_8703_;
                }
            }
            1 => {
                v___x_8696_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_8696_, 0, v_val_8692_);
                if v_isShared_8695_ == 0 {
                    lean_ctor_set(v___x_8694_, 0, v___x_8696_);
                    v___x_8698_ = v___x_8694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8700_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8700_, 0, v___x_8696_);
                    v___x_8698_ = v_reuseFailAlloc_8700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8699_ = lean_apply_2(v_toPure_8690_, lean_box(0), v___x_8698_);
                return v___x_8699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withSaveParentDeclInfoContext___redArg(
    mut v_inst_8704_: *mut LeanObject,
    mut v_inst_8705_: *mut LeanObject,
    mut v_inst_8706_: *mut LeanObject,
    mut v_inst_8707_: *mut LeanObject,
    mut v_x_8708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8714_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8709_ = lean_ctor_get(v_inst_8704_, 0);
    v_toBind_8710_ = lean_ctor_get(v_inst_8704_, 1);
    v_toPure_8711_ = lean_ctor_get(v_toApplicative_8709_, 1);
    lean_inc(v_toPure_8711_);
    v___f_8712_ = lean_alloc_closure(
        l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8712_, 0, v_toPure_8711_);
    lean_inc(v_toBind_8710_);
    v___x_8713_ = lean_apply_4(
        v_toBind_8710_,
        lean_box(0),
        lean_box(0),
        v_inst_8707_,
        v___f_8712_,
    );
    v___x_8714_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(
            v_inst_8704_,
            v_inst_8705_,
            v_inst_8706_,
            v_x_8708_,
            v___x_8713_,
        );
    return v___x_8714_;
}
pub unsafe fn l_Lean_Elab_withSaveParentDeclInfoContext(
    mut v_m_8715_: *mut LeanObject,
    mut v_inst_8716_: *mut LeanObject,
    mut v_inst_8717_: *mut LeanObject,
    mut v_00_u03b1_8718_: *mut LeanObject,
    mut v_inst_8719_: *mut LeanObject,
    mut v_inst_8720_: *mut LeanObject,
    mut v_x_8721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8722_: *mut LeanObject = core::ptr::null_mut();
    v___x_8722_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(
        v_inst_8716_,
        v_inst_8717_,
        v_inst_8719_,
        v_inst_8720_,
        v_x_8721_,
    );
    return v___x_8722_;
}
pub unsafe fn l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(
    mut v_toPure_8723_: *mut LeanObject,
    mut v_autoImplicits_8724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8727_: *mut LeanObject = core::ptr::null_mut();
    v___x_8725_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_8725_, 0, v_autoImplicits_8724_);
    v___x_8726_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8726_, 0, v___x_8725_);
    v___x_8727_ = lean_apply_2(v_toPure_8723_, lean_box(0), v___x_8726_);
    return v___x_8727_;
}
pub unsafe fn l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(
    mut v_inst_8728_: *mut LeanObject,
    mut v_inst_8729_: *mut LeanObject,
    mut v_inst_8730_: *mut LeanObject,
    mut v_inst_8731_: *mut LeanObject,
    mut v_x_8732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8738_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8733_ = lean_ctor_get(v_inst_8728_, 0);
    v_toBind_8734_ = lean_ctor_get(v_inst_8728_, 1);
    v_toPure_8735_ = lean_ctor_get(v_toApplicative_8733_, 1);
    lean_inc(v_toPure_8735_);
    v___f_8736_ = lean_alloc_closure(
        l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8736_, 0, v_toPure_8735_);
    lean_inc(v_toBind_8734_);
    v___x_8737_ = lean_apply_4(
        v_toBind_8734_,
        lean_box(0),
        lean_box(0),
        v_inst_8731_,
        v___f_8736_,
    );
    v___x_8738_ =
        l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(
            v_inst_8728_,
            v_inst_8729_,
            v_inst_8730_,
            v_x_8732_,
            v___x_8737_,
        );
    return v___x_8738_;
}
pub unsafe fn l_Lean_Elab_withSaveAutoImplicitInfoContext(
    mut v_m_8739_: *mut LeanObject,
    mut v_inst_8740_: *mut LeanObject,
    mut v_inst_8741_: *mut LeanObject,
    mut v_00_u03b1_8742_: *mut LeanObject,
    mut v_inst_8743_: *mut LeanObject,
    mut v_inst_8744_: *mut LeanObject,
    mut v_x_8745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8746_: *mut LeanObject = core::ptr::null_mut();
    v___x_8746_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(
        v_inst_8740_,
        v_inst_8741_,
        v_inst_8743_,
        v_inst_8744_,
        v_x_8745_,
    );
    return v___x_8746_;
}
pub unsafe fn l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(
    mut v___x_8747_: *mut LeanObject,
    mut v___x_8748_: *mut LeanObject,
    mut v_mvarId_8749_: *mut LeanObject,
    mut v_toPure_8750_: *mut LeanObject,
    mut v_____do__lift_8751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_assignment_8752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8754_: *mut LeanObject = core::ptr::null_mut();
    v_assignment_8752_ = lean_ctor_get(v_____do__lift_8751_, 0);
    v___x_8753_ = l_Lean_PersistentHashMap_find_x3f___redArg(
        v___x_8747_,
        v___x_8748_,
        v_assignment_8752_,
        v_mvarId_8749_,
    );
    v___x_8754_ = lean_apply_2(v_toPure_8750_, lean_box(0), v___x_8753_);
    return v___x_8754_;
}
pub unsafe fn l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(
    mut v___x_8755_: *mut LeanObject,
    mut v___x_8756_: *mut LeanObject,
    mut v_mvarId_8757_: *mut LeanObject,
    mut v_toPure_8758_: *mut LeanObject,
    mut v_____do__lift_8759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8760_: *mut LeanObject = core::ptr::null_mut();
    v_res_8760_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(
        v___x_8755_,
        v___x_8756_,
        v_mvarId_8757_,
        v_toPure_8758_,
        v_____do__lift_8759_,
    );
    lean_dec_ref(v_____do__lift_8759_);
    return v_res_8760_;
}
pub unsafe fn l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(
    mut v_inst_8763_: *mut LeanObject,
    mut v_inst_8764_: *mut LeanObject,
    mut v_mvarId_8765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8773_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8766_ = lean_ctor_get(v_inst_8763_, 0);
    lean_inc_ref(v_toApplicative_8766_);
    v_toBind_8767_ = lean_ctor_get(v_inst_8763_, 1);
    lean_inc(v_toBind_8767_);
    lean_dec_ref(v_inst_8763_);
    v_getInfoState_8768_ = lean_ctor_get(v_inst_8764_, 0);
    lean_inc(v_getInfoState_8768_);
    lean_dec_ref(v_inst_8764_);
    v_toPure_8769_ = lean_ctor_get(v_toApplicative_8766_, 1);
    lean_inc(v_toPure_8769_);
    lean_dec_ref(v_toApplicative_8766_);
    v___x_8770_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0;
    v___x_8771_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1;
    v___f_8772_ = lean_alloc_closure(
        l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_8772_, 0, v___x_8770_);
    lean_closure_set(v___f_8772_, 1, v___x_8771_);
    lean_closure_set(v___f_8772_, 2, v_mvarId_8765_);
    lean_closure_set(v___f_8772_, 3, v_toPure_8769_);
    v___x_8773_ = lean_apply_4(
        v_toBind_8767_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_8768_,
        v___f_8772_,
    );
    return v___x_8773_;
}
pub unsafe fn l_Lean_Elab_getInfoHoleIdAssignment_x3f(
    mut v_m_8774_: *mut LeanObject,
    mut v_inst_8775_: *mut LeanObject,
    mut v_inst_8776_: *mut LeanObject,
    mut v_mvarId_8777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8778_: *mut LeanObject = core::ptr::null_mut();
    v___x_8778_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(
        v_inst_8775_,
        v_inst_8776_,
        v_mvarId_8777_,
    );
    return v___x_8778_;
}
pub unsafe fn l_Lean_Elab_assignInfoHoleId___redArg___lam__0(
    mut v_mvarId_8779_: *mut LeanObject,
    mut v_infoTree_8780_: *mut LeanObject,
    mut v_s_8781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_8782_: u8 = 0;
    let mut v_assignment_8783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_8785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8788_: u8 = 0;
    let mut v___x_8789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_enabled_8782_ = lean_ctor_get_uint8(
                    v_s_8781_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_8783_ = lean_ctor_get(v_s_8781_, 0);
                v_lazyAssignment_8784_ = lean_ctor_get(v_s_8781_, 1);
                v_trees_8785_ = lean_ctor_get(v_s_8781_, 2);
                v_isSharedCheck_8795_ = (!lean_is_exclusive(v_s_8781_)) as u8;
                if v_isSharedCheck_8795_ == 0 {
                    v___x_8787_ = v_s_8781_;
                    v_isShared_8788_ = v_isSharedCheck_8795_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_trees_8785_);
                    lean_inc(v_lazyAssignment_8784_);
                    lean_inc(v_assignment_8783_);
                    lean_dec(v_s_8781_);
                    v___x_8787_ = lean_box(0);
                    v_isShared_8788_ = v_isSharedCheck_8795_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8789_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0;
                v___x_8790_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1;
                v___x_8791_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___x_8789_,
                    v___x_8790_,
                    v_assignment_8783_,
                    v_mvarId_8779_,
                    v_infoTree_8780_,
                );
                if v_isShared_8788_ == 0 {
                    lean_ctor_set(v___x_8787_, 0, v___x_8791_);
                    v___x_8793_ = v___x_8787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8794_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8794_, 0, v___x_8791_);
                    lean_ctor_set(v_reuseFailAlloc_8794_, 1, v_lazyAssignment_8784_);
                    lean_ctor_set(v_reuseFailAlloc_8794_, 2, v_trees_8785_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8794_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_8782_,
                    );
                    v___x_8793_ = v_reuseFailAlloc_8794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2() -> *mut LeanObject
{
    let mut v___x_8798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8803_: *mut LeanObject = core::ptr::null_mut();
    v___x_8798_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1;
    v___x_8799_ = lean_unsigned_to_nat(2);
    v___x_8800_ = lean_unsigned_to_nat(491);
    v___x_8801_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0;
    v___x_8802_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f___closed__1;
    v___x_8803_ = l_mkPanicMessageWithDecl(
        v___x_8802_,
        v___x_8801_,
        v___x_8800_,
        v___x_8799_,
        v___x_8798_,
    );
    return v___x_8803_;
}
pub unsafe fn l_Lean_Elab_assignInfoHoleId___redArg___lam__1(
    mut v_inst_8804_: *mut LeanObject,
    mut v___f_8805_: *mut LeanObject,
    mut v_inst_8806_: *mut LeanObject,
    mut v_____do__lift_8807_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_8807_) == 0 {
        let mut v_modifyInfoState_8808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8809_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_8806_);
        v_modifyInfoState_8808_ = lean_ctor_get(v_inst_8804_, 1);
        lean_inc(v_modifyInfoState_8808_);
        lean_dec_ref(v_inst_8804_);
        v___x_8809_ = lean_apply_1(v_modifyInfoState_8808_, v___f_8805_);
        return v___x_8809_;
    } else {
        let mut v___x_8810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8811_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8813_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_8805_);
        lean_dec_ref(v_inst_8804_);
        v___x_8810_ = lean_box(0);
        v___x_8811_ = l_instInhabitedOfMonad___redArg(v_inst_8806_, v___x_8810_);
        v___x_8812_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_once
            ),
            _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2,
        );
        v___x_8813_ = l_panic___redArg(v___x_8811_, v___x_8812_);
        lean_dec(v___x_8811_);
        return v___x_8813_;
    }
}
pub unsafe fn l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(
    mut v_inst_8814_: *mut LeanObject,
    mut v___f_8815_: *mut LeanObject,
    mut v_inst_8816_: *mut LeanObject,
    mut v_____do__lift_8817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8818_: *mut LeanObject = core::ptr::null_mut();
    v_res_8818_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(
        v_inst_8814_,
        v___f_8815_,
        v_inst_8816_,
        v_____do__lift_8817_,
    );
    lean_dec(v_____do__lift_8817_);
    return v_res_8818_;
}
pub unsafe fn l_Lean_Elab_assignInfoHoleId___redArg(
    mut v_inst_8819_: *mut LeanObject,
    mut v_inst_8820_: *mut LeanObject,
    mut v_mvarId_8821_: *mut LeanObject,
    mut v_infoTree_8822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_8823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8827_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_8823_ = lean_ctor_get(v_inst_8819_, 1);
    lean_inc(v_toBind_8823_);
    lean_inc(v_mvarId_8821_);
    v___f_8824_ = lean_alloc_closure(
        l_Lean_Elab_assignInfoHoleId___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8824_, 0, v_mvarId_8821_);
    lean_closure_set(v___f_8824_, 1, v_infoTree_8822_);
    lean_inc_ref(v_inst_8819_);
    lean_inc_ref(v_inst_8820_);
    v___f_8825_ = lean_alloc_closure(
        l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8825_, 0, v_inst_8820_);
    lean_closure_set(v___f_8825_, 1, v___f_8824_);
    lean_closure_set(v___f_8825_, 2, v_inst_8819_);
    v___x_8826_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(
        v_inst_8819_,
        v_inst_8820_,
        v_mvarId_8821_,
    );
    v___x_8827_ = lean_apply_4(
        v_toBind_8823_,
        lean_box(0),
        lean_box(0),
        v___x_8826_,
        v___f_8825_,
    );
    return v___x_8827_;
}
pub unsafe fn l_Lean_Elab_assignInfoHoleId(
    mut v_m_8828_: *mut LeanObject,
    mut v_inst_8829_: *mut LeanObject,
    mut v_inst_8830_: *mut LeanObject,
    mut v_mvarId_8831_: *mut LeanObject,
    mut v_infoTree_8832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8833_: *mut LeanObject = core::ptr::null_mut();
    v___x_8833_ = l_Lean_Elab_assignInfoHoleId___redArg(
        v_inst_8829_,
        v_inst_8830_,
        v_mvarId_8831_,
        v_infoTree_8832_,
    );
    return v___x_8833_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(
    mut v_stx_8834_: *mut LeanObject,
    mut v_output_8835_: *mut LeanObject,
    mut v_toPure_8836_: *mut LeanObject,
    mut v_____do__lift_8837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8840_: *mut LeanObject = core::ptr::null_mut();
    v___x_8838_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_8838_, 0, v_____do__lift_8837_);
    lean_ctor_set(v___x_8838_, 1, v_stx_8834_);
    lean_ctor_set(v___x_8838_, 2, v_output_8835_);
    v___x_8839_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_8839_, 0, v___x_8838_);
    v___x_8840_ = lean_apply_2(v_toPure_8836_, lean_box(0), v___x_8839_);
    return v___x_8840_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___redArg(
    mut v_inst_8841_: *mut LeanObject,
    mut v_inst_8842_: *mut LeanObject,
    mut v_inst_8843_: *mut LeanObject,
    mut v_inst_8844_: *mut LeanObject,
    mut v_stx_8845_: *mut LeanObject,
    mut v_output_8846_: *mut LeanObject,
    mut v_x_8847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mkInfo_8852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8854_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8848_ = lean_ctor_get(v_inst_8842_, 0);
    v_toBind_8849_ = lean_ctor_get(v_inst_8842_, 1);
    v_toPure_8850_ = lean_ctor_get(v_toApplicative_8848_, 1);
    lean_inc_n(v_toPure_8850_, 2);
    v___f_8851_ = lean_alloc_closure(
        l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8851_, 0, v_stx_8845_);
    lean_closure_set(v___f_8851_, 1, v_output_8846_);
    lean_closure_set(v___f_8851_, 2, v_toPure_8850_);
    lean_inc_n(v_toBind_8849_, 2);
    v_mkInfo_8852_ = lean_apply_4(
        v_toBind_8849_,
        lean_box(0),
        lean_box(0),
        v_inst_8844_,
        v___f_8851_,
    );
    v___f_8853_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_8853_, 0, v_toPure_8850_);
    lean_closure_set(v___f_8853_, 1, v_toBind_8849_);
    lean_closure_set(v___f_8853_, 2, v_mkInfo_8852_);
    v___x_8854_ = l_Lean_Elab_withInfoTreeContext___redArg(
        v_inst_8842_,
        v_inst_8843_,
        v_inst_8841_,
        v_x_8847_,
        v___f_8853_,
    );
    return v___x_8854_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo(
    mut v_m_8855_: *mut LeanObject,
    mut v_00_u03b1_8856_: *mut LeanObject,
    mut v_inst_8857_: *mut LeanObject,
    mut v_inst_8858_: *mut LeanObject,
    mut v_inst_8859_: *mut LeanObject,
    mut v_inst_8860_: *mut LeanObject,
    mut v_stx_8861_: *mut LeanObject,
    mut v_output_8862_: *mut LeanObject,
    mut v_x_8863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8864_: *mut LeanObject = core::ptr::null_mut();
    v___x_8864_ = l_Lean_Elab_withMacroExpansionInfo___redArg(
        v_inst_8857_,
        v_inst_8858_,
        v_inst_8859_,
        v_inst_8860_,
        v_stx_8861_,
        v_output_8862_,
        v_x_8863_,
    );
    return v___x_8864_;
}
pub unsafe fn l_Lean_Elab_withInfoHole___redArg___lam__1(
    mut v_treesSaved_8865_: *mut LeanObject,
    mut v_mvarId_8866_: *mut LeanObject,
    mut v_s_8867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_trees_8868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_8869_: u8 = 0;
    let mut v_assignment_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8874_: u8 = 0;
    let mut v_size_8875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8877_: u8 = 0;
    let mut v___x_8879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_trees_8868_ = lean_ctor_get(v_s_8867_, 2);
                v_enabled_8869_ = lean_ctor_get_uint8(
                    v_s_8867_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_8870_ = lean_ctor_get(v_s_8867_, 0);
                v_lazyAssignment_8871_ = lean_ctor_get(v_s_8867_, 1);
                v_isSharedCheck_8891_ = (!lean_is_exclusive(v_s_8867_)) as u8;
                if v_isSharedCheck_8891_ == 0 {
                    v___x_8873_ = v_s_8867_;
                    v_isShared_8874_ = v_isSharedCheck_8891_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_trees_8868_);
                    lean_inc(v_lazyAssignment_8871_);
                    lean_inc(v_assignment_8870_);
                    lean_dec(v_s_8867_);
                    v___x_8873_ = lean_box(0);
                    v_isShared_8874_ = v_isSharedCheck_8891_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_size_8875_ = lean_ctor_get(v_trees_8868_, 2);
                v___x_8876_ = lean_unsigned_to_nat(0);
                v___x_8877_ = lean_nat_dec_lt(v___x_8876_, v_size_8875_);
                if v___x_8877_ == 0 {
                    lean_dec_ref(v_trees_8868_);
                    lean_dec(v_mvarId_8866_);
                    if v_isShared_8874_ == 0 {
                        lean_ctor_set(v___x_8873_, 2, v_treesSaved_8865_);
                        v___x_8879_ = v___x_8873_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8880_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8880_, 0, v_assignment_8870_);
                        lean_ctor_set(v_reuseFailAlloc_8880_, 1, v_lazyAssignment_8871_);
                        lean_ctor_set(v_reuseFailAlloc_8880_, 2, v_treesSaved_8865_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_8880_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_enabled_8869_,
                        );
                        v___x_8879_ = v_reuseFailAlloc_8880_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_8881_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0;
                    v___x_8882_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1;
                    v___x_8883_ = l_Lean_Elab_instInhabitedInfoTree_default;
                    v___x_8884_ = lean_unsigned_to_nat(1);
                    v___x_8885_ = lean_nat_sub(v_size_8875_, v___x_8884_);
                    v___x_8886_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_8883_,
                        v_trees_8868_,
                        v___x_8885_,
                    );
                    lean_dec(v___x_8885_);
                    lean_dec_ref(v_trees_8868_);
                    v___x_8887_ = l_Lean_PersistentHashMap_insert___redArg(
                        v___x_8881_,
                        v___x_8882_,
                        v_assignment_8870_,
                        v_mvarId_8866_,
                        v___x_8886_,
                    );
                    if v_isShared_8874_ == 0 {
                        lean_ctor_set(v___x_8873_, 2, v_treesSaved_8865_);
                        lean_ctor_set(v___x_8873_, 0, v___x_8887_);
                        v___x_8889_ = v___x_8873_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8890_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8890_, 0, v___x_8887_);
                        lean_ctor_set(v_reuseFailAlloc_8890_, 1, v_lazyAssignment_8871_);
                        lean_ctor_set(v_reuseFailAlloc_8890_, 2, v_treesSaved_8865_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_8890_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_enabled_8869_,
                        );
                        v___x_8889_ = v_reuseFailAlloc_8890_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8879_;
            }
            3 => {
                return v___x_8889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoHole___redArg___lam__0(
    mut v_modifyInfoState_8892_: *mut LeanObject,
    mut v___f_8893_: *mut LeanObject,
    mut v_x_8894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8895_: *mut LeanObject = core::ptr::null_mut();
    v___x_8895_ = lean_apply_1(v_modifyInfoState_8892_, v___f_8893_);
    return v___x_8895_;
}
pub unsafe fn l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(
    mut v_modifyInfoState_8896_: *mut LeanObject,
    mut v___f_8897_: *mut LeanObject,
    mut v_x_8898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8899_: *mut LeanObject = core::ptr::null_mut();
    v_res_8899_ =
        l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_8896_, v___f_8897_, v_x_8898_);
    lean_dec(v_x_8898_);
    return v_res_8899_;
}
pub unsafe fn l_Lean_Elab_withInfoHole___redArg___lam__2(
    mut v_toApplicative_8900_: *mut LeanObject,
    mut v_mvarId_8901_: *mut LeanObject,
    mut v_modifyInfoState_8902_: *mut LeanObject,
    mut v_inst_8903_: *mut LeanObject,
    mut v_x_8904_: *mut LeanObject,
    mut v___f_8905_: *mut LeanObject,
    mut v_treesSaved_8906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toFunctor_8907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_8908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8912_: *mut LeanObject = core::ptr::null_mut();
    v_toFunctor_8907_ = lean_ctor_get(v_toApplicative_8900_, 0);
    lean_inc_ref(v_toFunctor_8907_);
    lean_dec_ref(v_toApplicative_8900_);
    v_map_8908_ = lean_ctor_get(v_toFunctor_8907_, 0);
    lean_inc(v_map_8908_);
    lean_dec_ref(v_toFunctor_8907_);
    v___f_8909_ = lean_alloc_closure(
        l_Lean_Elab_withInfoHole___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8909_, 0, v_treesSaved_8906_);
    lean_closure_set(v___f_8909_, 1, v_mvarId_8901_);
    v___f_8910_ = lean_alloc_closure(
        l_Lean_Elab_withInfoHole___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_8910_, 0, v_modifyInfoState_8902_);
    lean_closure_set(v___f_8910_, 1, v___f_8909_);
    v___x_8911_ = lean_apply_4(
        v_inst_8903_,
        lean_box(0),
        lean_box(0),
        v_x_8904_,
        v___f_8910_,
    );
    v___x_8912_ = lean_apply_4(
        v_map_8908_,
        lean_box(0),
        lean_box(0),
        v___f_8905_,
        v___x_8911_,
    );
    return v___x_8912_;
}
pub unsafe fn l_Lean_Elab_withInfoHole___redArg(
    mut v_inst_8913_: *mut LeanObject,
    mut v_inst_8914_: *mut LeanObject,
    mut v_inst_8915_: *mut LeanObject,
    mut v_mvarId_8916_: *mut LeanObject,
    mut v_x_8917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_8920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_8921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8925_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8918_ = lean_ctor_get(v_inst_8914_, 0);
    v_toBind_8919_ = lean_ctor_get(v_inst_8914_, 1);
    lean_inc_n(v_toBind_8919_, 2);
    v_getInfoState_8920_ = lean_ctor_get(v_inst_8915_, 0);
    lean_inc(v_getInfoState_8920_);
    v_modifyInfoState_8921_ = lean_ctor_get(v_inst_8915_, 1);
    v___f_8922_ = l_Lean_Elab_withInfoContext_x27___redArg___closed__0;
    lean_inc(v_x_8917_);
    lean_inc(v_modifyInfoState_8921_);
    lean_inc_ref(v_toApplicative_8918_);
    v___f_8923_ = lean_alloc_closure(
        l_Lean_Elab_withInfoHole___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_8923_, 0, v_toApplicative_8918_);
    lean_closure_set(v___f_8923_, 1, v_mvarId_8916_);
    lean_closure_set(v___f_8923_, 2, v_modifyInfoState_8921_);
    lean_closure_set(v___f_8923_, 3, v_inst_8913_);
    lean_closure_set(v___f_8923_, 4, v_x_8917_);
    lean_closure_set(v___f_8923_, 5, v___f_8922_);
    v___f_8924_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_8924_, 0, v_x_8917_);
    lean_closure_set(v___f_8924_, 1, v_inst_8914_);
    lean_closure_set(v___f_8924_, 2, v_inst_8915_);
    lean_closure_set(v___f_8924_, 3, v_toBind_8919_);
    lean_closure_set(v___f_8924_, 4, v___f_8923_);
    v___x_8925_ = lean_apply_4(
        v_toBind_8919_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_8920_,
        v___f_8924_,
    );
    return v___x_8925_;
}
pub unsafe fn l_Lean_Elab_withInfoHole(
    mut v_m_8926_: *mut LeanObject,
    mut v_00_u03b1_8927_: *mut LeanObject,
    mut v_inst_8928_: *mut LeanObject,
    mut v_inst_8929_: *mut LeanObject,
    mut v_inst_8930_: *mut LeanObject,
    mut v_mvarId_8931_: *mut LeanObject,
    mut v_x_8932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_8935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_8936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8933_ = lean_ctor_get(v_inst_8929_, 0);
    v_toBind_8934_ = lean_ctor_get(v_inst_8929_, 1);
    lean_inc_n(v_toBind_8934_, 2);
    v_getInfoState_8935_ = lean_ctor_get(v_inst_8930_, 0);
    lean_inc(v_getInfoState_8935_);
    v_modifyInfoState_8936_ = lean_ctor_get(v_inst_8930_, 1);
    v___f_8937_ = l_Lean_Elab_withInfoContext_x27___redArg___closed__0;
    lean_inc(v_x_8932_);
    lean_inc(v_modifyInfoState_8936_);
    lean_inc_ref(v_toApplicative_8933_);
    v___f_8938_ = lean_alloc_closure(
        l_Lean_Elab_withInfoHole___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_8938_, 0, v_toApplicative_8933_);
    lean_closure_set(v___f_8938_, 1, v_mvarId_8931_);
    lean_closure_set(v___f_8938_, 2, v_modifyInfoState_8936_);
    lean_closure_set(v___f_8938_, 3, v_inst_8928_);
    lean_closure_set(v___f_8938_, 4, v_x_8932_);
    lean_closure_set(v___f_8938_, 5, v___f_8937_);
    v___f_8939_ = lean_alloc_closure(
        l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_8939_, 0, v_x_8932_);
    lean_closure_set(v___f_8939_, 1, v_inst_8929_);
    lean_closure_set(v___f_8939_, 2, v_inst_8930_);
    lean_closure_set(v___f_8939_, 3, v_toBind_8934_);
    lean_closure_set(v___f_8939_, 4, v___f_8938_);
    v___x_8940_ = lean_apply_4(
        v_toBind_8934_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_8935_,
        v___f_8939_,
    );
    return v___x_8940_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___redArg___lam__0(
    mut v_flag_8941_: u8,
    mut v_s_8942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_assignment_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_8945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8948_: u8 = 0;
    let mut v___x_8950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_assignment_8943_ = lean_ctor_get(v_s_8942_, 0);
                v_lazyAssignment_8944_ = lean_ctor_get(v_s_8942_, 1);
                v_trees_8945_ = lean_ctor_get(v_s_8942_, 2);
                v_isSharedCheck_8952_ = (!lean_is_exclusive(v_s_8942_)) as u8;
                if v_isSharedCheck_8952_ == 0 {
                    v___x_8947_ = v_s_8942_;
                    v_isShared_8948_ = v_isSharedCheck_8952_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_trees_8945_);
                    lean_inc(v_lazyAssignment_8944_);
                    lean_inc(v_assignment_8943_);
                    lean_dec(v_s_8942_);
                    v___x_8947_ = lean_box(0);
                    v_isShared_8948_ = v_isSharedCheck_8952_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_8948_ == 0 {
                    v___x_8950_ = v___x_8947_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8951_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8951_, 0, v_assignment_8943_);
                    lean_ctor_set(v_reuseFailAlloc_8951_, 1, v_lazyAssignment_8944_);
                    lean_ctor_set(v_reuseFailAlloc_8951_, 2, v_trees_8945_);
                    v___x_8950_ = v_reuseFailAlloc_8951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_8950_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_flag_8941_,
                );
                return v___x_8950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(
    mut v_flag_8953_: *mut LeanObject,
    mut v_s_8954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_8955_: u8 = 0;
    let mut v_res_8956_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_8955_ = (lean_unbox(v_flag_8953_) as u8);
    v_res_8956_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_8955_, v_s_8954_);
    return v_res_8956_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___redArg(
    mut v_inst_8957_: *mut LeanObject,
    mut v_flag_8958_: u8,
) -> *mut LeanObject {
    let mut v_modifyInfoState_8959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: *mut LeanObject = core::ptr::null_mut();
    v_modifyInfoState_8959_ = lean_ctor_get(v_inst_8957_, 1);
    lean_inc(v_modifyInfoState_8959_);
    lean_dec_ref(v_inst_8957_);
    v___x_8960_ = lean_box((v_flag_8958_) as usize);
    v___f_8961_ = lean_alloc_closure(
        l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8961_, 0, v___x_8960_);
    v___x_8962_ = lean_apply_1(v_modifyInfoState_8959_, v___f_8961_);
    return v___x_8962_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___redArg___boxed(
    mut v_inst_8963_: *mut LeanObject,
    mut v_flag_8964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_8965_: u8 = 0;
    let mut v_res_8966_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_8965_ = (lean_unbox(v_flag_8964_) as u8);
    v_res_8966_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_8963_, v_flag_boxed_8965_);
    return v_res_8966_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree(
    mut v_m_8967_: *mut LeanObject,
    mut v_inst_8968_: *mut LeanObject,
    mut v_flag_8969_: u8,
) -> *mut LeanObject {
    let mut v___x_8970_: *mut LeanObject = core::ptr::null_mut();
    v___x_8970_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_8968_, v_flag_8969_);
    return v___x_8970_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___boxed(
    mut v_m_8971_: *mut LeanObject,
    mut v_inst_8972_: *mut LeanObject,
    mut v_flag_8973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_8974_: u8 = 0;
    let mut v_res_8975_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_8974_ = (lean_unbox(v_flag_8973_) as u8);
    v_res_8975_ = l_Lean_Elab_enableInfoTree(v_m_8971_, v_inst_8972_, v_flag_boxed_8974_);
    return v_res_8975_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__0(
    mut v_x_8976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_8977_: *mut LeanObject = core::ptr::null_mut();
    v_fst_8977_ = lean_ctor_get(v_x_8976_, 0);
    lean_inc(v_fst_8977_);
    return v_fst_8977_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(
    mut v_x_8978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8979_: *mut LeanObject = core::ptr::null_mut();
    v_res_8979_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_8978_);
    lean_dec_ref(v_x_8978_);
    return v_res_8979_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__1(
    mut v_x_8980_: *mut LeanObject,
    mut v_____r_8981_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_8980_);
    return v_x_8980_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(
    mut v_x_8982_: *mut LeanObject,
    mut v_____r_8983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8984_: *mut LeanObject = core::ptr::null_mut();
    v_res_8984_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_8982_, v_____r_8983_);
    lean_dec(v_x_8982_);
    return v_res_8984_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__2(
    mut v___x_8985_: *mut LeanObject,
    mut v_x_8986_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_8985_);
    return v___x_8985_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(
    mut v___x_8987_: *mut LeanObject,
    mut v_x_8988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8989_: *mut LeanObject = core::ptr::null_mut();
    v_res_8989_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_8987_, v_x_8988_);
    lean_dec(v_x_8988_);
    lean_dec(v___x_8987_);
    return v_res_8989_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__3(
    mut v_toFunctor_8990_: *mut LeanObject,
    mut v_inst_8991_: *mut LeanObject,
    mut v_flag_8992_: u8,
    mut v_toBind_8993_: *mut LeanObject,
    mut v___f_8994_: *mut LeanObject,
    mut v_inst_8995_: *mut LeanObject,
    mut v___f_8996_: *mut LeanObject,
    mut v_____do__lift_8997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_enabled_8998_: u8 = 0;
    let mut v_map_8999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_9004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: *mut LeanObject = core::ptr::null_mut();
    v_enabled_8998_ = lean_ctor_get_uint8(
        v_____do__lift_8997_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_map_8999_ = lean_ctor_get(v_toFunctor_8990_, 0);
    lean_inc(v_map_8999_);
    lean_dec_ref(v_toFunctor_8990_);
    lean_inc_ref(v_inst_8991_);
    v___x_9000_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_8991_, v_flag_8992_);
    v___x_9001_ = lean_apply_4(
        v_toBind_8993_,
        lean_box(0),
        lean_box(0),
        v___x_9000_,
        v___f_8994_,
    );
    v___x_9002_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_8991_, v_enabled_8998_);
    v___f_9003_ = lean_alloc_closure(
        l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9003_, 0, v___x_9002_);
    v_y_9004_ = lean_apply_4(
        v_inst_8995_,
        lean_box(0),
        lean_box(0),
        v___x_9001_,
        v___f_9003_,
    );
    v___x_9005_ = lean_apply_4(
        v_map_8999_,
        lean_box(0),
        lean_box(0),
        v___f_8996_,
        v_y_9004_,
    );
    return v___x_9005_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(
    mut v_toFunctor_9006_: *mut LeanObject,
    mut v_inst_9007_: *mut LeanObject,
    mut v_flag_9008_: *mut LeanObject,
    mut v_toBind_9009_: *mut LeanObject,
    mut v___f_9010_: *mut LeanObject,
    mut v_inst_9011_: *mut LeanObject,
    mut v___f_9012_: *mut LeanObject,
    mut v_____do__lift_9013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_9014_: u8 = 0;
    let mut v_res_9015_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_9014_ = (lean_unbox(v_flag_9008_) as u8);
    v_res_9015_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(
        v_toFunctor_9006_,
        v_inst_9007_,
        v_flag_boxed_9014_,
        v_toBind_9009_,
        v___f_9010_,
        v_inst_9011_,
        v___f_9012_,
        v_____do__lift_9013_,
    );
    lean_dec_ref(v_____do__lift_9013_);
    return v_res_9015_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg(
    mut v_inst_9017_: *mut LeanObject,
    mut v_inst_9018_: *mut LeanObject,
    mut v_inst_9019_: *mut LeanObject,
    mut v_flag_9020_: u8,
    mut v_x_9021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_9022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_9023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_9025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9030_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_9022_ = lean_ctor_get(v_inst_9017_, 0);
    lean_inc_ref(v_toApplicative_9022_);
    v_toBind_9023_ = lean_ctor_get(v_inst_9017_, 1);
    lean_inc_n(v_toBind_9023_, 2);
    lean_dec_ref(v_inst_9017_);
    v_getInfoState_9024_ = lean_ctor_get(v_inst_9018_, 0);
    lean_inc(v_getInfoState_9024_);
    v_toFunctor_9025_ = lean_ctor_get(v_toApplicative_9022_, 0);
    lean_inc_ref(v_toFunctor_9025_);
    lean_dec_ref(v_toApplicative_9022_);
    v___f_9026_ = l_Lean_Elab_withEnableInfoTree___redArg___closed__0;
    v___f_9027_ = lean_alloc_closure(
        l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9027_, 0, v_x_9021_);
    v___x_9028_ = lean_box((v_flag_9020_) as usize);
    v___f_9029_ = lean_alloc_closure(
        l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_9029_, 0, v_toFunctor_9025_);
    lean_closure_set(v___f_9029_, 1, v_inst_9018_);
    lean_closure_set(v___f_9029_, 2, v___x_9028_);
    lean_closure_set(v___f_9029_, 3, v_toBind_9023_);
    lean_closure_set(v___f_9029_, 4, v___f_9027_);
    lean_closure_set(v___f_9029_, 5, v_inst_9019_);
    lean_closure_set(v___f_9029_, 6, v___f_9026_);
    v___x_9030_ = lean_apply_4(
        v_toBind_9023_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_9024_,
        v___f_9029_,
    );
    return v___x_9030_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___redArg___boxed(
    mut v_inst_9031_: *mut LeanObject,
    mut v_inst_9032_: *mut LeanObject,
    mut v_inst_9033_: *mut LeanObject,
    mut v_flag_9034_: *mut LeanObject,
    mut v_x_9035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_9036_: u8 = 0;
    let mut v_res_9037_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_9036_ = (lean_unbox(v_flag_9034_) as u8);
    v_res_9037_ = l_Lean_Elab_withEnableInfoTree___redArg(
        v_inst_9031_,
        v_inst_9032_,
        v_inst_9033_,
        v_flag_boxed_9036_,
        v_x_9035_,
    );
    return v_res_9037_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree(
    mut v_m_9038_: *mut LeanObject,
    mut v_00_u03b1_9039_: *mut LeanObject,
    mut v_inst_9040_: *mut LeanObject,
    mut v_inst_9041_: *mut LeanObject,
    mut v_inst_9042_: *mut LeanObject,
    mut v_flag_9043_: u8,
    mut v_x_9044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9045_: *mut LeanObject = core::ptr::null_mut();
    v___x_9045_ = l_Lean_Elab_withEnableInfoTree___redArg(
        v_inst_9040_,
        v_inst_9041_,
        v_inst_9042_,
        v_flag_9043_,
        v_x_9044_,
    );
    return v___x_9045_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___boxed(
    mut v_m_9046_: *mut LeanObject,
    mut v_00_u03b1_9047_: *mut LeanObject,
    mut v_inst_9048_: *mut LeanObject,
    mut v_inst_9049_: *mut LeanObject,
    mut v_inst_9050_: *mut LeanObject,
    mut v_flag_9051_: *mut LeanObject,
    mut v_x_9052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flag_boxed_9053_: u8 = 0;
    let mut v_res_9054_: *mut LeanObject = core::ptr::null_mut();
    v_flag_boxed_9053_ = (lean_unbox(v_flag_9051_) as u8);
    v_res_9054_ = l_Lean_Elab_withEnableInfoTree(
        v_m_9046_,
        v_00_u03b1_9047_,
        v_inst_9048_,
        v_inst_9049_,
        v_inst_9050_,
        v_flag_boxed_9053_,
        v_x_9052_,
    );
    return v_res_9054_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___redArg___lam__0(
    mut v_toPure_9055_: *mut LeanObject,
    mut v_____do__lift_9056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_trees_9057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9058_: *mut LeanObject = core::ptr::null_mut();
    v_trees_9057_ = lean_ctor_get(v_____do__lift_9056_, 2);
    lean_inc_ref(v_trees_9057_);
    lean_dec_ref(v_____do__lift_9056_);
    v___x_9058_ = lean_apply_2(v_toPure_9055_, lean_box(0), v_trees_9057_);
    return v___x_9058_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___redArg(
    mut v_inst_9059_: *mut LeanObject,
    mut v_inst_9060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_9061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_9062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInfoState_9063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_9064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9066_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_9061_ = lean_ctor_get(v_inst_9060_, 0);
    lean_inc_ref(v_toApplicative_9061_);
    v_toBind_9062_ = lean_ctor_get(v_inst_9060_, 1);
    lean_inc(v_toBind_9062_);
    lean_dec_ref(v_inst_9060_);
    v_getInfoState_9063_ = lean_ctor_get(v_inst_9059_, 0);
    lean_inc(v_getInfoState_9063_);
    lean_dec_ref(v_inst_9059_);
    v_toPure_9064_ = lean_ctor_get(v_toApplicative_9061_, 1);
    lean_inc(v_toPure_9064_);
    lean_dec_ref(v_toApplicative_9061_);
    v___f_9065_ = lean_alloc_closure(
        l_Lean_Elab_getInfoTrees___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_9065_, 0, v_toPure_9064_);
    v___x_9066_ = lean_apply_4(
        v_toBind_9062_,
        lean_box(0),
        lean_box(0),
        v_getInfoState_9063_,
        v___f_9065_,
    );
    return v___x_9066_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees(
    mut v_m_9067_: *mut LeanObject,
    mut v_inst_9068_: *mut LeanObject,
    mut v_inst_9069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9070_: *mut LeanObject = core::ptr::null_mut();
    v___x_9070_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_9068_, v_inst_9069_);
    return v___x_9070_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_InfoTree_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Task(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ReservedNameAction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_InfoTree_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_InfoTree_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Task(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ReservedNameAction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_InfoTree_Main(builtin);
}
