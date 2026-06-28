// Lean compiler output
// Module: Lean.Meta.UnificationHint
// Imports: Lean.Meta.SynthInstance
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instantiateValueLevelParams, l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Data::Format::l_Lean_instToFormatName__lean___lam__0;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_value_x3f,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isMVar, l_Lean_instBEqBinderInfo_beq,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp,
    l_Lean_Meta_Config_toConfigWithKey, l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_getResetPostponed___redArg, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_lambdaMetaTelescope, l_Lean_Meta_mkFreshLevelMVar, l_Lean_Meta_processPostponed,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_empty,
    l_Lean_Meta_DiscrTree_format___redArg, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Main::{
    l_Lean_Meta_DiscrTree_getMatch___redArg, l_Lean_Meta_DiscrTree_mkPath,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    initialize_Lean_Meta_SynthInstance, l_Lean_Meta_trySynthInstance,
    runtime_initialize_Lean_Meta_SynthInstance,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_is_expr_def_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6, lean_box,
    lean_box_float, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64,
    lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_float, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedUnificationHintEntry_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedUnificationHintEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedUnificationHintEntry_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedUnificationHints_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedUnificationHints_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedUnificationHints: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instToFormatUnificationHints___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToFormatName__lean___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instToFormatUnificationHints___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToFormatUnificationHints___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instToFormatUnificationHints___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_instToFormatUnificationHints___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToFormatUnificationHints___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instToFormatUnificationHints___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToFormatUnificationHints___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instToFormatUnificationHints: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToFormatUnificationHints___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        72058693566333185 as *mut LeanObject,
        65793 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0_value)
        as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 72, 105, 110, 116, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,10538288938178694228 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_UnificationHints_add as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 104, 105, 110, 116, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0_value: LeanStringObject<59> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 59, m_capacity: 59, m_length: 58, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 104, 105, 110, 116, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0_value
) as *mut LeanObject;
pub static l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 104, 105, 110, 116, 44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 117, 110, 105, 102, 121, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 32, 108, 101, 102, 116, 45, 104, 97, 110, 100, 45, 115, 105, 100, 101, 0]};
static mut l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0_value) as *mut LeanObject;
static mut l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [10, 119, 105, 116, 104, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 45, 115, 105, 100, 101, 0]};
static mut l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2_value) as *mut LeanObject;
static mut l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0_value:
    LeanStringObject<65> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 65,
    m_capacity: 65,
    m_length: 64,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110,
        32, 104, 105, 110, 116, 44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 117, 110,
        105, 102, 121, 32, 112, 97, 116, 116, 101, 114, 110, 32, 108, 101, 102, 116, 45, 104, 97,
        110, 100, 45, 115, 105, 100, 101, 0,
    ],
};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_addUnificationHint___lam__0___closed__0_value: LeanStringObject<50> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111,
            110, 32, 104, 105, 110, 116, 44, 32, 105, 116, 32, 109, 117, 115, 116, 32, 98, 101, 32,
            97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_addUnificationHint___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_addUnificationHint___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_addUnificationHint___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_addUnificationHint___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [85, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 72, 105, 110, 116, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,285071825514688585 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,1723683115418896652 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,7396637680698215565 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,5678387469907706693 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,1809012063655821644 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,5576173491387027493 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,1447052166056598512 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,1704751498352329340 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,5174343671476120979 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 95, 104, 105, 110, 116, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject,11164110816768596393 as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 104, 105, 110, 116, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0: u64 = 0;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 115, 68, 101, 102, 69, 113, 0]};
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 105, 110, 116, 0]};
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__3_value) as *mut LeanObject,784036993727507922 as *mut LeanObject] };
pub static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__4_value) as *mut LeanObject,13700240677916803955 as *mut LeanObject] };
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__6_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [32, 115, 117, 99, 99, 101, 101, 100, 101, 100, 44, 32, 97, 112, 112, 108, 121, 105, 110, 103, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 115, 0]};
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9_value) as *mut LeanObject;
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 105, 110, 116, 32, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 97, 116, 32, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 61, 63, 61, 32, 0]};
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4: f64 = 0.0;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0: f64 = 0.0;
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0()
-> *mut LeanObject {
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    v___x_3020_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
    return v___x_3020_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedUnificationHints_default() -> *mut LeanObject {
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    v___x_3021_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedUnificationHints_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0,
    );
    return v___x_3021_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedUnificationHints() -> *mut LeanObject {
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    v___x_3022_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedUnificationHints_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0,
    );
    return v___x_3022_;
}
pub unsafe fn l_Lean_Meta_instToFormatUnificationHints___lam__0(
    mut v___f_3023_: *mut LeanObject,
    mut v_h_3024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    v___x_3025_ = l_Lean_Meta_DiscrTree_format___redArg(v___f_3023_, v_h_3024_);
    return v___x_3025_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1()
-> *mut LeanObject {
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    v___x_3036_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__0;
    v___x_3037_ = l_Lean_Meta_Config_toConfigWithKey(v___x_3036_);
    return v___x_3037_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config() -> *mut LeanObject {
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    v___x_3038_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1_once
        ),
        _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config___closed__1,
    );
    return v___x_3038_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(
    mut v_x_3039_: *mut LeanObject,
    mut v_x_3040_: *mut LeanObject,
    mut v_x_3041_: *mut LeanObject,
    mut v_x_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3043_ = lean_ctor_get(v_x_3039_, 0);
                v_vs_3044_ = lean_ctor_get(v_x_3039_, 1);
                v_isSharedCheck_3068_ = (!lean_is_exclusive(v_x_3039_)) as u8;
                if v_isSharedCheck_3068_ == 0 {
                    v___x_3046_ = v_x_3039_;
                    v_isShared_3047_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3044_);
                    lean_inc(v_ks_3043_);
                    lean_dec(v_x_3039_);
                    v___x_3046_ = lean_box(0);
                    v_isShared_3047_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3048_ = lean_array_get_size(v_ks_3043_);
                v___x_3049_ = lean_nat_dec_lt(v_x_3040_, v___x_3048_);
                if v___x_3049_ == 0 {
                    lean_dec(v_x_3040_);
                    v___x_3050_ = lean_array_push(v_ks_3043_, v_x_3041_);
                    v___x_3051_ = lean_array_push(v_vs_3044_, v_x_3042_);
                    if v_isShared_3047_ == 0 {
                        lean_ctor_set(v___x_3046_, 1, v___x_3051_);
                        lean_ctor_set(v___x_3046_, 0, v___x_3050_);
                        v___x_3053_ = v___x_3046_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3050_);
                        lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3051_);
                        v___x_3053_ = v_reuseFailAlloc_3054_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3055_ = lean_array_fget_borrowed(v_ks_3043_, v_x_3040_);
                    v___x_3056_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3041_, v_k_x27_3055_);
                    if v___x_3056_ == 0 {
                        if v_isShared_3047_ == 0 {
                            v___x_3058_ = v___x_3046_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_ks_3043_);
                            lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_vs_3044_);
                            v___x_3058_ = v_reuseFailAlloc_3062_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3063_ = lean_array_fset(v_ks_3043_, v_x_3040_, v_x_3041_);
                        v___x_3064_ = lean_array_fset(v_vs_3044_, v_x_3040_, v_x_3042_);
                        lean_dec(v_x_3040_);
                        if v_isShared_3047_ == 0 {
                            lean_ctor_set(v___x_3046_, 1, v___x_3064_);
                            lean_ctor_set(v___x_3046_, 0, v___x_3063_);
                            v___x_3066_ = v___x_3046_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3063_);
                            lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_3064_);
                            v___x_3066_ = v_reuseFailAlloc_3067_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3053_;
            }
            3 => {
                v___x_3059_ = lean_unsigned_to_nat(1);
                v___x_3060_ = lean_nat_add(v_x_3040_, v___x_3059_);
                lean_dec(v_x_3040_);
                v_x_3039_ = v___x_3058_;
                v_x_3040_ = v___x_3060_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_n_3069_: *mut LeanObject,
    mut v_k_3070_: *mut LeanObject,
    mut v_v_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    v___x_3072_ = lean_unsigned_to_nat(0);
    v___x_3073_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_3069_, v___x_3072_, v_k_3070_, v_v_3071_);
    return v___x_3073_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: usize = 0;
    let mut v___x_3076_: usize = 0;
    v___x_3074_ = 5usize;
    v___x_3075_ = 1usize;
    v___x_3076_ = lean_usize_shift_left(v___x_3075_, v___x_3074_);
    return v___x_3076_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_3077_: usize = 0;
    let mut v___x_3078_: usize = 0;
    let mut v___x_3079_: usize = 0;
    v___x_3077_ = 1usize;
    v___x_3078_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__0);
    v___x_3079_ = lean_usize_sub(v___x_3078_, v___x_3077_);
    return v___x_3079_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    v___x_3080_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3080_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(
    mut v_x_3081_: *mut LeanObject,
    mut v_x_3082_: usize,
    mut v_x_3083_: usize,
    mut v_x_3084_: *mut LeanObject,
    mut v_x_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: usize = 0;
    let mut v___x_3088_: usize = 0;
    let mut v___x_3089_: usize = 0;
    let mut v___x_3090_: usize = 0;
    let mut v_j_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3096_: u8 = 0;
    let mut v_v_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3117_: u8 = 0;
    let mut v_node_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3122_: usize = 0;
    let mut v___x_3123_: usize = 0;
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3128_: u8 = 0;
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3130_: u8 = 0;
    let mut v_unused_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: u8 = 0;
    let mut v_ks_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: usize = 0;
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    let mut v_reuseFailAlloc_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3081_) == 0 {
                    v_es_3086_ = lean_ctor_get(v_x_3081_, 0);
                    v___x_3087_ = 5usize;
                    v___x_3088_ = 1usize;
                    v___x_3089_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_3090_ = lean_usize_land(v_x_3082_, v___x_3089_);
                    v_j_3091_ = lean_usize_to_nat(v___x_3090_);
                    v___x_3092_ = lean_array_get_size(v_es_3086_);
                    v___x_3093_ = lean_nat_dec_lt(v_j_3091_, v___x_3092_);
                    if v___x_3093_ == 0 {
                        lean_dec(v_j_3091_);
                        lean_dec(v_x_3085_);
                        lean_dec(v_x_3084_);
                        return v_x_3081_;
                    } else {
                        lean_inc_ref(v_es_3086_);
                        v_isSharedCheck_3130_ = (!lean_is_exclusive(v_x_3081_)) as u8;
                        if v_isSharedCheck_3130_ == 0 {
                            v_unused_3131_ = lean_ctor_get(v_x_3081_, 0);
                            lean_dec(v_unused_3131_);
                            v___x_3095_ = v_x_3081_;
                            v_isShared_3096_ = v_isSharedCheck_3130_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3081_);
                            v___x_3095_ = lean_box(0);
                            v_isShared_3096_ = v_isSharedCheck_3130_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3132_ = lean_ctor_get(v_x_3081_, 0);
                    v_vs_3133_ = lean_ctor_get(v_x_3081_, 1);
                    v_isSharedCheck_3153_ = (!lean_is_exclusive(v_x_3081_)) as u8;
                    if v_isSharedCheck_3153_ == 0 {
                        v___x_3135_ = v_x_3081_;
                        v_isShared_3136_ = v_isSharedCheck_3153_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3133_);
                        lean_inc(v_ks_3132_);
                        lean_dec(v_x_3081_);
                        v___x_3135_ = lean_box(0);
                        v_isShared_3136_ = v_isSharedCheck_3153_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3097_ = lean_array_fget(v_es_3086_, v_j_3091_);
                v___x_3098_ = lean_box(0);
                v_xs_x27_3099_ = lean_array_fset(v_es_3086_, v_j_3091_, v___x_3098_);
                match lean_obj_tag(v_v_3097_) {
                    0 => {
                        v_key_3106_ = lean_ctor_get(v_v_3097_, 0);
                        v_val_3107_ = lean_ctor_get(v_v_3097_, 1);
                        v_isSharedCheck_3117_ = (!lean_is_exclusive(v_v_3097_)) as u8;
                        if v_isSharedCheck_3117_ == 0 {
                            v___x_3109_ = v_v_3097_;
                            v_isShared_3110_ = v_isSharedCheck_3117_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3107_);
                            lean_inc(v_key_3106_);
                            lean_dec(v_v_3097_);
                            v___x_3109_ = lean_box(0);
                            v_isShared_3110_ = v_isSharedCheck_3117_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3118_ = lean_ctor_get(v_v_3097_, 0);
                        v_isSharedCheck_3128_ = (!lean_is_exclusive(v_v_3097_)) as u8;
                        if v_isSharedCheck_3128_ == 0 {
                            v___x_3120_ = v_v_3097_;
                            v_isShared_3121_ = v_isSharedCheck_3128_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3118_);
                            lean_dec(v_v_3097_);
                            v___x_3120_ = lean_box(0);
                            v_isShared_3121_ = v_isSharedCheck_3128_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3129_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3129_, 0, v_x_3084_);
                        lean_ctor_set(v___x_3129_, 1, v_x_3085_);
                        v___y_3101_ = v___x_3129_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3102_ = lean_array_fset(v_xs_x27_3099_, v_j_3091_, v___y_3101_);
                lean_dec(v_j_3091_);
                if v_isShared_3096_ == 0 {
                    lean_ctor_set(v___x_3095_, 0, v___x_3102_);
                    v___x_3104_ = v___x_3095_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
                    v___x_3104_ = v_reuseFailAlloc_3105_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3104_;
            }
            4 => {
                v___x_3111_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3084_, v_key_3106_);
                if v___x_3111_ == 0 {
                    lean_del_object(v___x_3109_);
                    v___x_3112_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3106_,
                        v_val_3107_,
                        v_x_3084_,
                        v_x_3085_,
                    );
                    v___x_3113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3113_, 0, v___x_3112_);
                    v___y_3101_ = v___x_3113_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3107_);
                    lean_dec(v_key_3106_);
                    if v_isShared_3110_ == 0 {
                        lean_ctor_set(v___x_3109_, 1, v_x_3085_);
                        lean_ctor_set(v___x_3109_, 0, v_x_3084_);
                        v___x_3115_ = v___x_3109_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_x_3084_);
                        lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_x_3085_);
                        v___x_3115_ = v_reuseFailAlloc_3116_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3101_ = v___x_3115_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3122_ = lean_usize_shift_right(v_x_3082_, v___x_3087_);
                v___x_3123_ = lean_usize_add(v_x_3083_, v___x_3088_);
                v___x_3124_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_node_3118_, v___x_3122_, v___x_3123_, v_x_3084_, v_x_3085_);
                if v_isShared_3121_ == 0 {
                    lean_ctor_set(v___x_3120_, 0, v___x_3124_);
                    v___x_3126_ = v___x_3120_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
                    v___x_3126_ = v_reuseFailAlloc_3127_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3101_ = v___x_3126_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3136_ == 0 {
                    v___x_3138_ = v___x_3135_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_ks_3132_);
                    lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_vs_3133_);
                    v___x_3138_ = v_reuseFailAlloc_3152_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3139_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(v___x_3138_, v_x_3084_, v_x_3085_);
                v___x_3147_ = 7usize;
                v___x_3148_ = lean_usize_dec_le(v___x_3147_, v_x_3083_);
                if v___x_3148_ == 0 {
                    v___x_3149_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3139_);
                    v___x_3150_ = lean_unsigned_to_nat(4);
                    v___x_3151_ = lean_nat_dec_lt(v___x_3149_, v___x_3150_);
                    lean_dec(v___x_3149_);
                    v___y_3141_ = v___x_3151_;
                    state = 10;
                    continue;
                } else {
                    v___y_3141_ = v___x_3148_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3141_ == 0 {
                    v_ks_3142_ = lean_ctor_get(v_newNode_3139_, 0);
                    lean_inc_ref(v_ks_3142_);
                    v_vs_3143_ = lean_ctor_get(v_newNode_3139_, 1);
                    lean_inc_ref(v_vs_3143_);
                    lean_dec_ref(v_newNode_3139_);
                    v___x_3144_ = lean_unsigned_to_nat(0);
                    v___x_3145_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__2);
                    v___x_3146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_x_3083_, v_ks_3142_, v_vs_3143_, v___x_3144_, v___x_3145_);
                    lean_dec_ref(v_vs_3143_);
                    lean_dec_ref(v_ks_3142_);
                    return v___x_3146_;
                } else {
                    return v_newNode_3139_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_depth_3154_: usize,
    mut v_keys_3155_: *mut LeanObject,
    mut v_vals_3156_: *mut LeanObject,
    mut v_i_3157_: *mut LeanObject,
    mut v_entries_3158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: u8 = 0;
    let mut v_k_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u64 = 0;
    let mut v_h_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: usize = 0;
    let mut v___x_3168_: usize = 0;
    let mut v___x_3169_: usize = 0;
    let mut v_h_3170_: usize = 0;
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3159_ = lean_array_get_size(v_keys_3155_);
                v___x_3160_ = lean_nat_dec_lt(v_i_3157_, v___x_3159_);
                if v___x_3160_ == 0 {
                    lean_dec(v_i_3157_);
                    return v_entries_3158_;
                } else {
                    v_k_3161_ = lean_array_fget_borrowed(v_keys_3155_, v_i_3157_);
                    v_v_3162_ = lean_array_fget_borrowed(v_vals_3156_, v_i_3157_);
                    v___x_3163_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_3161_);
                    v_h_3164_ = lean_uint64_to_usize(v___x_3163_);
                    v___x_3165_ = 5usize;
                    v___x_3166_ = lean_unsigned_to_nat(1);
                    v___x_3167_ = 1usize;
                    v___x_3168_ = lean_usize_sub(v_depth_3154_, v___x_3167_);
                    v___x_3169_ = lean_usize_mul(v___x_3165_, v___x_3168_);
                    v_h_3170_ = lean_usize_shift_right(v_h_3164_, v___x_3169_);
                    v___x_3171_ = lean_nat_add(v_i_3157_, v___x_3166_);
                    lean_dec(v_i_3157_);
                    lean_inc(v_v_3162_);
                    lean_inc(v_k_3161_);
                    v___x_3172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_entries_3158_, v_h_3170_, v_depth_3154_, v_k_3161_, v_v_3162_);
                    v_i_3157_ = v___x_3171_;
                    v_entries_3158_ = v___x_3172_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_depth_3174_: *mut LeanObject,
    mut v_keys_3175_: *mut LeanObject,
    mut v_vals_3176_: *mut LeanObject,
    mut v_i_3177_: *mut LeanObject,
    mut v_entries_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3179_: usize = 0;
    let mut v_res_3180_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3179_ = lean_unbox_usize(v_depth_3174_);
    lean_dec(v_depth_3174_);
    v_res_3180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_3179_, v_keys_3175_, v_vals_3176_, v_i_3177_, v_entries_3178_);
    lean_dec_ref(v_vals_3176_);
    lean_dec_ref(v_keys_3175_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_3181_: *mut LeanObject,
    mut v_x_3182_: *mut LeanObject,
    mut v_x_3183_: *mut LeanObject,
    mut v_x_3184_: *mut LeanObject,
    mut v_x_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1605__boxed_3186_: usize = 0;
    let mut v_x_1606__boxed_3187_: usize = 0;
    let mut v_res_3188_: *mut LeanObject = core::ptr::null_mut();
    v_x_1605__boxed_3186_ = lean_unbox_usize(v_x_3182_);
    lean_dec(v_x_3182_);
    v_x_1606__boxed_3187_ = lean_unbox_usize(v_x_3183_);
    lean_dec(v_x_3183_);
    v_res_3188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_3181_, v_x_1605__boxed_3186_, v_x_1606__boxed_3187_, v_x_3184_, v_x_3185_);
    return v_res_3188_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(
    mut v_x_3189_: *mut LeanObject,
    mut v_x_3190_: *mut LeanObject,
    mut v_x_3191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3192_: u64 = 0;
    let mut v___x_3193_: usize = 0;
    let mut v___x_3194_: usize = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    v___x_3192_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_3190_);
    v___x_3193_ = lean_uint64_to_usize(v___x_3192_);
    v___x_3194_ = 1usize;
    v___x_3195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_3189_, v___x_3193_, v___x_3194_, v_x_3190_, v_x_3191_);
    return v___x_3195_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(
    mut v_a_3196_: *mut LeanObject,
    mut v_b_3197_: *mut LeanObject,
) -> u8 {
    let mut v_fst_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: u8 = 0;
    v_fst_3198_ = lean_ctor_get(v_a_3196_, 0);
    v_fst_3199_ = lean_ctor_get(v_b_3197_, 0);
    v___x_3200_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_3198_, v_fst_3199_);
    return v___x_3200_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1___boxed(
    mut v_a_3201_: *mut LeanObject,
    mut v_b_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3203_: u8 = 0;
    let mut v_r_3204_: *mut LeanObject = core::ptr::null_mut();
    v_res_3203_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_a_3201_, v_b_3202_);
    lean_dec_ref(v_b_3202_);
    lean_dec_ref(v_a_3201_);
    v_r_3204_ = lean_box((v_res_3203_) as usize);
    return v_r_3204_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(
    mut v_x_3205_: *mut LeanObject,
    mut v_keys_3206_: *mut LeanObject,
    mut v_v_3207_: *mut LeanObject,
    mut v_k_3208_: *mut LeanObject,
    mut v_x_3209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    v___x_3210_ = lean_unsigned_to_nat(1);
    v___x_3211_ = lean_nat_add(v_x_3205_, v___x_3210_);
    v_c_3212_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        lean_box(0),
        v_keys_3206_,
        v_v_3207_,
        v___x_3211_,
    );
    lean_dec(v___x_3211_);
    v___x_3213_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3213_, 0, v_k_3208_);
    lean_ctor_set(v___x_3213_, 1, v_c_3212_);
    return v___x_3213_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0___boxed(
    mut v_x_3214_: *mut LeanObject,
    mut v_keys_3215_: *mut LeanObject,
    mut v_v_3216_: *mut LeanObject,
    mut v_k_3217_: *mut LeanObject,
    mut v_x_3218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3219_: *mut LeanObject = core::ptr::null_mut();
    v_res_3219_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_3214_, v_keys_3215_, v_v_3216_, v_k_3217_, v_x_3218_);
    lean_dec_ref(v_keys_3215_);
    lean_dec(v_x_3214_);
    return v_res_3219_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5_spec__10(
    mut v_vs_3220_: *mut LeanObject,
    mut v_v_3221_: *mut LeanObject,
    mut v_i_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3223_ = lean_array_get_size(v_vs_3220_);
                v___x_3224_ = lean_nat_dec_lt(v_i_3222_, v___x_3223_);
                if v___x_3224_ == 0 {
                    lean_dec(v_i_3222_);
                    v___x_3225_ = lean_array_push(v_vs_3220_, v_v_3221_);
                    return v___x_3225_;
                } else {
                    v___x_3226_ = lean_array_fget_borrowed(v_vs_3220_, v_i_3222_);
                    v___x_3227_ = lean_name_eq(v_v_3221_, v___x_3226_);
                    if v___x_3227_ == 0 {
                        v___x_3228_ = lean_unsigned_to_nat(1);
                        v___x_3229_ = lean_nat_add(v_i_3222_, v___x_3228_);
                        lean_dec(v_i_3222_);
                        v_i_3222_ = v___x_3229_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3231_ = lean_array_fset(v_vs_3220_, v_i_3222_, v_v_3221_);
                        lean_dec(v_i_3222_);
                        return v___x_3231_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5(
    mut v_vs_3232_: *mut LeanObject,
    mut v_v_3233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    v___x_3234_ = lean_unsigned_to_nat(0);
    v___x_3235_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5_spec__10(v_vs_3232_, v_v_3233_, v___x_3234_);
    return v___x_3235_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(
    mut v_x_3240_: *mut LeanObject,
    mut v_keys_3241_: *mut LeanObject,
    mut v_v_3242_: *mut LeanObject,
    mut v_k_3243_: *mut LeanObject,
    mut v_as_3244_: *mut LeanObject,
    mut v_k_3245_: *mut LeanObject,
    mut v_x_3246_: *mut LeanObject,
    mut v_x_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_midVal_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    let mut v_snd_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut v_unused_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: u8 = 0;
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3248_ = lean_nat_add(v_x_3246_, v_x_3247_);
                v___x_3249_ = lean_unsigned_to_nat(1);
                v_mid_3250_ = lean_nat_shiftr(v___x_3248_, v___x_3249_);
                lean_dec(v___x_3248_);
                v_midVal_3251_ = lean_array_fget(v_as_3244_, v_mid_3250_);
                v___x_3252_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_midVal_3251_, v_k_3245_);
                if v___x_3252_ == 0 {
                    lean_dec(v_x_3247_);
                    v___x_3253_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_3245_, v_midVal_3251_);
                    if v___x_3253_ == 0 {
                        lean_dec(v_x_3246_);
                        v___x_3254_ = lean_array_get_size(v_as_3244_);
                        v___x_3255_ = lean_nat_dec_lt(v_mid_3250_, v___x_3254_);
                        if v___x_3255_ == 0 {
                            lean_dec(v_midVal_3251_);
                            lean_dec(v_mid_3250_);
                            lean_dec(v_k_3243_);
                            lean_dec(v_v_3242_);
                            return v_as_3244_;
                        } else {
                            v_snd_3256_ = lean_ctor_get(v_midVal_3251_, 1);
                            v_isSharedCheck_3268_ = (!lean_is_exclusive(v_midVal_3251_)) as u8;
                            if v_isSharedCheck_3268_ == 0 {
                                v_unused_3269_ = lean_ctor_get(v_midVal_3251_, 0);
                                lean_dec(v_unused_3269_);
                                v___x_3258_ = v_midVal_3251_;
                                v_isShared_3259_ = v_isSharedCheck_3268_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_3256_);
                                lean_dec(v_midVal_3251_);
                                v___x_3258_ = lean_box(0);
                                v_isShared_3259_ = v_isSharedCheck_3268_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_midVal_3251_);
                        v_x_3247_ = v_mid_3250_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_midVal_3251_);
                    v___x_3271_ = lean_nat_dec_eq(v_mid_3250_, v_x_3246_);
                    if v___x_3271_ == 0 {
                        lean_dec(v_x_3246_);
                        v_x_3246_ = v_mid_3250_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_mid_3250_);
                        lean_dec(v_x_3247_);
                        v___x_3273_ = lean_nat_add(v_x_3240_, v___x_3249_);
                        v_c_3274_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_3241_, v_v_3242_, v___x_3273_);
                        lean_dec(v___x_3273_);
                        v___x_3275_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3275_, 0, v_k_3243_);
                        lean_ctor_set(v___x_3275_, 1, v_c_3274_);
                        v___x_3276_ = lean_nat_add(v_x_3246_, v___x_3249_);
                        lean_dec(v_x_3246_);
                        v_j_3277_ = lean_array_get_size(v_as_3244_);
                        v_as_3278_ = lean_array_push(v_as_3244_, v___x_3275_);
                        v___x_3279_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            lean_box(0),
                            v___x_3276_,
                            v_as_3278_,
                            v_j_3277_,
                        );
                        lean_dec(v___x_3276_);
                        return v___x_3279_;
                    }
                }
            }
            1 => {
                v___x_3260_ = lean_box(0);
                v_xs_x27_3261_ = lean_array_fset(v_as_3244_, v_mid_3250_, v___x_3260_);
                v___x_3262_ = lean_nat_add(v_x_3240_, v___x_3249_);
                v_c_3263_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_3241_, v_v_3242_, v___x_3262_, v_snd_3256_);
                lean_dec(v___x_3262_);
                if v_isShared_3259_ == 0 {
                    lean_ctor_set(v___x_3258_, 1, v_c_3263_);
                    lean_ctor_set(v___x_3258_, 0, v_k_3243_);
                    v___x_3265_ = v___x_3258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_k_3243_);
                    lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_c_3263_);
                    v___x_3265_ = v_reuseFailAlloc_3267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3266_ = lean_array_fset(v_xs_x27_3261_, v_mid_3250_, v___x_3265_);
                lean_dec(v_mid_3250_);
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(
    mut v_x_3280_: *mut LeanObject,
    mut v_keys_3281_: *mut LeanObject,
    mut v_v_3282_: *mut LeanObject,
    mut v_k_3283_: *mut LeanObject,
    mut v_as_3284_: *mut LeanObject,
    mut v_k_3285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    v___x_3286_ = lean_array_get_size(v_as_3284_);
    v___x_3287_ = lean_unsigned_to_nat(0);
    v___x_3288_ = lean_nat_dec_eq(v___x_3286_, v___x_3287_);
    if v___x_3288_ == 0 {
        let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3290_: u8 = 0;
        v___x_3289_ = lean_array_fget_borrowed(v_as_3284_, v___x_3287_);
        v___x_3290_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_3285_, v___x_3289_);
        if v___x_3290_ == 0 {
            let mut v___x_3291_: u8 = 0;
            v___x_3291_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v___x_3289_, v_k_3285_);
            if v___x_3291_ == 0 {
                let mut v___x_3292_: u8 = 0;
                v___x_3292_ = lean_nat_dec_lt(v___x_3287_, v___x_3286_);
                if v___x_3292_ == 0 {
                    lean_dec(v_k_3283_);
                    lean_dec(v_v_3282_);
                    return v_as_3284_;
                } else {
                    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_3294_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc(v___x_3289_);
                    v___x_3293_ = lean_box(0);
                    v_xs_x27_3294_ = lean_array_fset(v_as_3284_, v___x_3287_, v___x_3293_);
                    v___x_3295_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_3280_, v_keys_3281_, v_v_3282_, v_k_3283_, v___x_3289_);
                    v___x_3296_ = lean_array_fset(v_xs_x27_3294_, v___x_3287_, v___x_3295_);
                    return v___x_3296_;
                }
            } else {
                let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3300_: u8 = 0;
                v___x_3297_ = lean_unsigned_to_nat(1);
                v___x_3298_ = lean_nat_sub(v___x_3286_, v___x_3297_);
                v___x_3299_ = lean_array_fget_borrowed(v_as_3284_, v___x_3298_);
                v___x_3300_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v___x_3299_, v_k_3285_);
                if v___x_3300_ == 0 {
                    let mut v___x_3301_: u8 = 0;
                    v___x_3301_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__1(v_k_3285_, v___x_3299_);
                    if v___x_3301_ == 0 {
                        let mut v___x_3302_: u8 = 0;
                        v___x_3302_ = lean_nat_dec_lt(v___x_3298_, v___x_3286_);
                        if v___x_3302_ == 0 {
                            lean_dec(v___x_3298_);
                            lean_dec(v_k_3283_);
                            lean_dec(v_v_3282_);
                            return v_as_3284_;
                        } else {
                            let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_xs_x27_3304_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
                            lean_inc(v___x_3299_);
                            v___x_3303_ = lean_box(0);
                            v_xs_x27_3304_ = lean_array_fset(v_as_3284_, v___x_3298_, v___x_3303_);
                            v___x_3305_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_3280_, v_keys_3281_, v_v_3282_, v_k_3283_, v___x_3299_);
                            v___x_3306_ = lean_array_fset(v_xs_x27_3304_, v___x_3298_, v___x_3305_);
                            lean_dec(v___x_3298_);
                            return v___x_3306_;
                        }
                    } else {
                        let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
                        v___x_3307_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_3280_, v_keys_3281_, v_v_3282_, v_k_3283_, v_as_3284_, v_k_3285_, v___x_3287_, v___x_3298_);
                        return v___x_3307_;
                    }
                } else {
                    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_3298_);
                    v___x_3308_ = lean_box(0);
                    v___x_3309_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_3280_, v_keys_3281_, v_v_3282_, v_k_3283_, v___x_3308_);
                    v___x_3310_ = lean_array_push(v_as_3284_, v___x_3309_);
                    return v___x_3310_;
                }
            }
        } else {
            let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
            let mut v_as_3313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
            v___x_3311_ = lean_box(0);
            v___x_3312_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_3280_, v_keys_3281_, v_v_3282_, v_k_3283_, v___x_3311_);
            v_as_3313_ = lean_array_push(v_as_3284_, v___x_3312_);
            v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                lean_box(0),
                v___x_3287_,
                v_as_3313_,
                v___x_3286_,
            );
            return v___x_3314_;
        }
    } else {
        let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
        v___x_3315_ = lean_box(0);
        v___x_3316_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__0(v_x_3280_, v_keys_3281_, v_v_3282_, v_k_3283_, v___x_3315_);
        v___x_3317_ = lean_array_push(v_as_3284_, v___x_3316_);
        return v___x_3317_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(
    mut v_keys_3318_: *mut LeanObject,
    mut v_v_3319_: *mut LeanObject,
    mut v_x_3320_: *mut LeanObject,
    mut v_x_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_3322_ = lean_ctor_get(v_x_3321_, 0);
                v_children_3323_ = lean_ctor_get(v_x_3321_, 1);
                v_isSharedCheck_3340_ = (!lean_is_exclusive(v_x_3321_)) as u8;
                if v_isSharedCheck_3340_ == 0 {
                    v___x_3325_ = v_x_3321_;
                    v_isShared_3326_ = v_isSharedCheck_3340_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_children_3323_);
                    lean_inc(v_vs_3322_);
                    lean_dec(v_x_3321_);
                    v___x_3325_ = lean_box(0);
                    v_isShared_3326_ = v_isSharedCheck_3340_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3327_ = lean_array_get_size(v_keys_3318_);
                v___x_3328_ = lean_nat_dec_lt(v_x_3320_, v___x_3327_);
                if v___x_3328_ == 0 {
                    v___x_3329_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__5(v_vs_3322_, v_v_3319_);
                    if v_isShared_3326_ == 0 {
                        lean_ctor_set(v___x_3325_, 0, v___x_3329_);
                        v___x_3331_ = v___x_3325_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
                        lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_children_3323_);
                        v___x_3331_ = v_reuseFailAlloc_3332_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_3333_ = lean_array_fget_borrowed(v_keys_3318_, v_x_3320_);
                    v___x_3334_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___closed__1;
                    lean_inc_n(v_k_3333_, 2);
                    v___x_3335_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3335_, 0, v_k_3333_);
                    lean_ctor_set(v___x_3335_, 1, v___x_3334_);
                    v_c_3336_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(v_x_3320_, v_keys_3318_, v_v_3319_, v_k_3333_, v_children_3323_, v___x_3335_);
                    lean_dec_ref_known(v___x_3335_, 2);
                    if v_isShared_3326_ == 0 {
                        lean_ctor_set(v___x_3325_, 1, v_c_3336_);
                        v___x_3338_ = v___x_3325_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_vs_3322_);
                        lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_c_3336_);
                        v___x_3338_ = v_reuseFailAlloc_3339_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3331_;
            }
            3 => {
                return v___x_3338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(
    mut v_x_3341_: *mut LeanObject,
    mut v_keys_3342_: *mut LeanObject,
    mut v_v_3343_: *mut LeanObject,
    mut v_k_3344_: *mut LeanObject,
    mut v_x_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3349_: u8 = 0;
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3356_: u8 = 0;
    let mut v_unused_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3346_ = lean_ctor_get(v_x_3345_, 1);
                v_isSharedCheck_3356_ = (!lean_is_exclusive(v_x_3345_)) as u8;
                if v_isSharedCheck_3356_ == 0 {
                    v_unused_3357_ = lean_ctor_get(v_x_3345_, 0);
                    lean_dec(v_unused_3357_);
                    v___x_3348_ = v_x_3345_;
                    v_isShared_3349_ = v_isSharedCheck_3356_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3346_);
                    lean_dec(v_x_3345_);
                    v___x_3348_ = lean_box(0);
                    v_isShared_3349_ = v_isSharedCheck_3356_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3350_ = lean_unsigned_to_nat(1);
                v___x_3351_ = lean_nat_add(v_x_3341_, v___x_3350_);
                v_c_3352_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_3342_, v_v_3343_, v___x_3351_, v_snd_3346_);
                lean_dec(v___x_3351_);
                if v_isShared_3349_ == 0 {
                    lean_ctor_set(v___x_3348_, 1, v_c_3352_);
                    lean_ctor_set(v___x_3348_, 0, v_k_3344_);
                    v___x_3354_ = v___x_3348_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_k_3344_);
                    lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_c_3352_);
                    v___x_3354_ = v_reuseFailAlloc_3355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2___boxed(
    mut v_x_3358_: *mut LeanObject,
    mut v_keys_3359_: *mut LeanObject,
    mut v_v_3360_: *mut LeanObject,
    mut v_k_3361_: *mut LeanObject,
    mut v_x_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3363_: *mut LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___lam__2(v_x_3358_, v_keys_3359_, v_v_3360_, v_k_3361_, v_x_3362_);
    lean_dec_ref(v_keys_3359_);
    lean_dec(v_x_3358_);
    return v_res_3363_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2___boxed(
    mut v_keys_3364_: *mut LeanObject,
    mut v_v_3365_: *mut LeanObject,
    mut v_x_3366_: *mut LeanObject,
    mut v_x_3367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3368_: *mut LeanObject = core::ptr::null_mut();
    v_res_3368_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_3364_, v_v_3365_, v_x_3366_, v_x_3367_);
    lean_dec(v_x_3366_);
    lean_dec_ref(v_keys_3364_);
    return v_res_3368_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg___boxed(
    mut v_x_3369_: *mut LeanObject,
    mut v_keys_3370_: *mut LeanObject,
    mut v_v_3371_: *mut LeanObject,
    mut v_k_3372_: *mut LeanObject,
    mut v_as_3373_: *mut LeanObject,
    mut v_k_3374_: *mut LeanObject,
    mut v_x_3375_: *mut LeanObject,
    mut v_x_3376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3377_: *mut LeanObject = core::ptr::null_mut();
    v_res_3377_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_3369_, v_keys_3370_, v_v_3371_, v_k_3372_, v_as_3373_, v_k_3374_, v_x_3375_, v_x_3376_);
    lean_dec_ref(v_k_3374_);
    lean_dec_ref(v_keys_3370_);
    lean_dec(v_x_3369_);
    return v_res_3377_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6___boxed(
    mut v_x_3378_: *mut LeanObject,
    mut v_keys_3379_: *mut LeanObject,
    mut v_v_3380_: *mut LeanObject,
    mut v_k_3381_: *mut LeanObject,
    mut v_as_3382_: *mut LeanObject,
    mut v_k_3383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3384_: *mut LeanObject = core::ptr::null_mut();
    v_res_3384_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6(v_x_3378_, v_keys_3379_, v_v_3380_, v_k_3381_, v_as_3382_, v_k_3383_);
    lean_dec_ref(v_k_3383_);
    lean_dec_ref(v_keys_3379_);
    lean_dec(v_x_3378_);
    return v_res_3384_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    v___x_3385_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
    return v___x_3385_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(
    mut v_msg_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    v___x_3387_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3___closed__0);
    v___x_3388_ = lean_panic_fn_borrowed(v___x_3387_, v_msg_3386_);
    return v___x_3388_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_3389_: *mut LeanObject,
    mut v_vals_3390_: *mut LeanObject,
    mut v_i_3391_: *mut LeanObject,
    mut v_k_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3393_ = lean_array_get_size(v_keys_3389_);
                v___x_3394_ = lean_nat_dec_lt(v_i_3391_, v___x_3393_);
                if v___x_3394_ == 0 {
                    lean_dec(v_i_3391_);
                    v___x_3395_ = lean_box(0);
                    return v___x_3395_;
                } else {
                    v_k_x27_3396_ = lean_array_fget_borrowed(v_keys_3389_, v_i_3391_);
                    v___x_3397_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_3392_, v_k_x27_3396_);
                    if v___x_3397_ == 0 {
                        v___x_3398_ = lean_unsigned_to_nat(1);
                        v___x_3399_ = lean_nat_add(v_i_3391_, v___x_3398_);
                        lean_dec(v_i_3391_);
                        v_i_3391_ = v___x_3399_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3401_ = lean_array_fget_borrowed(v_vals_3390_, v_i_3391_);
                        lean_dec(v_i_3391_);
                        lean_inc(v___x_3401_);
                        v___x_3402_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3402_, 0, v___x_3401_);
                        return v___x_3402_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_3403_: *mut LeanObject,
    mut v_vals_3404_: *mut LeanObject,
    mut v_i_3405_: *mut LeanObject,
    mut v_k_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3407_: *mut LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3403_, v_vals_3404_, v_i_3405_, v_k_3406_);
    lean_dec(v_k_3406_);
    lean_dec_ref(v_vals_3404_);
    lean_dec_ref(v_keys_3403_);
    return v_res_3407_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(
    mut v_x_3408_: *mut LeanObject,
    mut v_x_3409_: usize,
    mut v_x_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: usize = 0;
    let mut v___x_3414_: usize = 0;
    let mut v___x_3415_: usize = 0;
    let mut v_j_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: u8 = 0;
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: usize = 0;
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3408_) == 0 {
                    v_es_3411_ = lean_ctor_get(v_x_3408_, 0);
                    v___x_3412_ = lean_box(2);
                    v___x_3413_ = 5usize;
                    v___x_3414_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_3415_ = lean_usize_land(v_x_3409_, v___x_3414_);
                    v_j_3416_ = lean_usize_to_nat(v___x_3415_);
                    v___x_3417_ = lean_array_get_borrowed(v___x_3412_, v_es_3411_, v_j_3416_);
                    lean_dec(v_j_3416_);
                    match lean_obj_tag(v___x_3417_) {
                        0 => {
                            v_key_3418_ = lean_ctor_get(v___x_3417_, 0);
                            v_val_3419_ = lean_ctor_get(v___x_3417_, 1);
                            v___x_3420_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_3410_, v_key_3418_);
                            if v___x_3420_ == 0 {
                                v___x_3421_ = lean_box(0);
                                return v___x_3421_;
                            } else {
                                lean_inc(v_val_3419_);
                                v___x_3422_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3422_, 0, v_val_3419_);
                                return v___x_3422_;
                            }
                        }
                        1 => {
                            v_node_3423_ = lean_ctor_get(v___x_3417_, 0);
                            v___x_3424_ = lean_usize_shift_right(v_x_3409_, v___x_3413_);
                            v_x_3408_ = v_node_3423_;
                            v_x_3409_ = v___x_3424_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3426_ = lean_box(0);
                            return v___x_3426_;
                        }
                    }
                } else {
                    v_ks_3427_ = lean_ctor_get(v_x_3408_, 0);
                    v_vs_3428_ = lean_ctor_get(v_x_3408_, 1);
                    v___x_3429_ = lean_unsigned_to_nat(0);
                    v___x_3430_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_3427_, v_vs_3428_, v___x_3429_, v_x_3410_);
                    return v___x_3430_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_3431_: *mut LeanObject,
    mut v_x_3432_: *mut LeanObject,
    mut v_x_3433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2052__boxed_3434_: usize = 0;
    let mut v_res_3435_: *mut LeanObject = core::ptr::null_mut();
    v_x_2052__boxed_3434_ = lean_unbox_usize(v_x_3432_);
    lean_dec(v_x_3432_);
    v_res_3435_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_3431_, v_x_2052__boxed_3434_, v_x_3433_);
    lean_dec(v_x_3433_);
    lean_dec_ref(v_x_3431_);
    return v_res_3435_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(
    mut v_x_3436_: *mut LeanObject,
    mut v_x_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3438_: u64 = 0;
    let mut v___x_3439_: usize = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3438_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_3437_);
    v___x_3439_ = lean_uint64_to_usize(v___x_3438_);
    v___x_3440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_3436_, v___x_3439_, v_x_3437_);
    return v___x_3440_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg___boxed(
    mut v_x_3441_: *mut LeanObject,
    mut v_x_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3443_: *mut LeanObject = core::ptr::null_mut();
    v_res_3443_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_3441_, v_x_3442_);
    lean_dec(v_x_3442_);
    lean_dec_ref(v_x_3441_);
    return v_res_3443_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    v___x_3447_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__2;
    v___x_3448_ = lean_unsigned_to_nat(23);
    v___x_3449_ = lean_unsigned_to_nat(166);
    v___x_3450_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__1;
    v___x_3451_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__0;
    v___x_3452_ = l_mkPanicMessageWithDecl(
        v___x_3451_,
        v___x_3450_,
        v___x_3449_,
        v___x_3448_,
        v___x_3447_,
    );
    return v___x_3452_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(
    mut v_d_3453_: *mut LeanObject,
    mut v_keys_3454_: *mut LeanObject,
    mut v_v_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    v___x_3456_ = lean_array_get_size(v_keys_3454_);
    v___x_3457_ = lean_unsigned_to_nat(0);
    v___x_3458_ = lean_nat_dec_eq(v___x_3456_, v___x_3457_);
    if v___x_3458_ == 0 {
        let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_3460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
        v___x_3459_ = lean_box(0);
        v_k_3460_ = lean_array_get_borrowed(v___x_3459_, v_keys_3454_, v___x_3457_);
        v___x_3461_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_d_3453_, v_k_3460_);
        if lean_obj_tag(v___x_3461_) == 0 {
            let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_3463_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
            v___x_3462_ = lean_unsigned_to_nat(1);
            v_c_3463_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                lean_box(0),
                v_keys_3454_,
                v_v_3455_,
                v___x_3462_,
            );
            lean_inc(v_k_3460_);
            v___x_3464_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_3453_, v_k_3460_, v_c_3463_);
            return v___x_3464_;
        } else {
            let mut v_val_3465_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_3467_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
            v_val_3465_ = lean_ctor_get(v___x_3461_, 0);
            lean_inc(v_val_3465_);
            lean_dec_ref_known(v___x_3461_, 1);
            v___x_3466_ = lean_unsigned_to_nat(1);
            v_c_3467_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2(v_keys_3454_, v_v_3455_, v___x_3466_, v_val_3465_);
            lean_inc(v_k_3460_);
            v___x_3468_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_d_3453_, v_k_3460_, v_c_3467_);
            return v___x_3468_;
        }
    } else {
        let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_v_3455_);
        lean_dec_ref(v_d_3453_);
        v___x_3469_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___closed__3);
        v___x_3470_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__3(v___x_3469_);
        return v___x_3470_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0___boxed(
    mut v_d_3471_: *mut LeanObject,
    mut v_keys_3472_: *mut LeanObject,
    mut v_v_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3474_: *mut LeanObject = core::ptr::null_mut();
    v_res_3474_ =
        l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(
            v_d_3471_,
            v_keys_3472_,
            v_v_3473_,
        );
    lean_dec_ref(v_keys_3472_);
    return v_res_3474_;
}
pub unsafe fn l_Lean_Meta_UnificationHints_add(
    mut v_hints_3475_: *mut LeanObject,
    mut v_e_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keys_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    v_keys_3477_ = lean_ctor_get(v_e_3476_, 0);
    lean_inc_ref(v_keys_3477_);
    v_val_3478_ = lean_ctor_get(v_e_3476_, 1);
    lean_inc(v_val_3478_);
    lean_dec_ref(v_e_3476_);
    v___x_3479_ =
        l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0(
            v_hints_3475_,
            v_keys_3477_,
            v_val_3478_,
        );
    lean_dec_ref(v_keys_3477_);
    return v___x_3479_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(
    mut v_00_u03b2_3480_: *mut LeanObject,
    mut v_x_3481_: *mut LeanObject,
    mut v_x_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    v___x_3483_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___redArg(v_x_3481_, v_x_3482_);
    return v___x_3483_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0___boxed(
    mut v_00_u03b2_3484_: *mut LeanObject,
    mut v_x_3485_: *mut LeanObject,
    mut v_x_3486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3487_: *mut LeanObject = core::ptr::null_mut();
    v_res_3487_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0(v_00_u03b2_3484_, v_x_3485_, v_x_3486_);
    lean_dec(v_x_3486_);
    lean_dec_ref(v_x_3485_);
    return v_res_3487_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1(
    mut v_00_u03b2_3488_: *mut LeanObject,
    mut v_x_3489_: *mut LeanObject,
    mut v_x_3490_: *mut LeanObject,
    mut v_x_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_3492_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1___redArg(v_x_3489_, v_x_3490_, v_x_3491_);
    return v___x_3492_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3493_: *mut LeanObject,
    mut v_x_3494_: *mut LeanObject,
    mut v_x_3495_: usize,
    mut v_x_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    v___x_3497_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___redArg(v_x_3494_, v_x_3495_, v_x_3496_);
    return v___x_3497_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3498_: *mut LeanObject,
    mut v_x_3499_: *mut LeanObject,
    mut v_x_3500_: *mut LeanObject,
    mut v_x_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2182__boxed_3502_: usize = 0;
    let mut v_res_3503_: *mut LeanObject = core::ptr::null_mut();
    v_x_2182__boxed_3502_ = lean_unbox_usize(v_x_3500_);
    lean_dec(v_x_3500_);
    v_res_3503_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1(v_00_u03b2_3498_, v_x_3499_, v_x_2182__boxed_3502_, v_x_3501_);
    lean_dec(v_x_3501_);
    lean_dec_ref(v_x_3499_);
    return v_res_3503_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3504_: *mut LeanObject,
    mut v_x_3505_: *mut LeanObject,
    mut v_x_3506_: usize,
    mut v_x_3507_: usize,
    mut v_x_3508_: *mut LeanObject,
    mut v_x_3509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    v___x_3510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___redArg(v_x_3505_, v_x_3506_, v_x_3507_, v_x_3508_, v_x_3509_);
    return v___x_3510_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3511_: *mut LeanObject,
    mut v_x_3512_: *mut LeanObject,
    mut v_x_3513_: *mut LeanObject,
    mut v_x_3514_: *mut LeanObject,
    mut v_x_3515_: *mut LeanObject,
    mut v_x_3516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2193__boxed_3517_: usize = 0;
    let mut v_x_2194__boxed_3518_: usize = 0;
    let mut v_res_3519_: *mut LeanObject = core::ptr::null_mut();
    v_x_2193__boxed_3517_ = lean_unbox_usize(v_x_3513_);
    lean_dec(v_x_3513_);
    v_x_2194__boxed_3518_ = lean_unbox_usize(v_x_3514_);
    lean_dec(v_x_3514_);
    v_res_3519_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3(v_00_u03b2_3511_, v_x_3512_, v_x_2193__boxed_3517_, v_x_2194__boxed_3518_, v_x_3515_, v_x_3516_);
    return v_res_3519_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3520_: *mut LeanObject,
    mut v_keys_3521_: *mut LeanObject,
    mut v_vals_3522_: *mut LeanObject,
    mut v_heq_3523_: *mut LeanObject,
    mut v_i_3524_: *mut LeanObject,
    mut v_k_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3521_, v_vals_3522_, v_i_3524_, v_k_3525_);
    return v___x_3526_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3527_: *mut LeanObject,
    mut v_keys_3528_: *mut LeanObject,
    mut v_vals_3529_: *mut LeanObject,
    mut v_heq_3530_: *mut LeanObject,
    mut v_i_3531_: *mut LeanObject,
    mut v_k_3532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3533_: *mut LeanObject = core::ptr::null_mut();
    v_res_3533_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3527_, v_keys_3528_, v_vals_3529_, v_heq_3530_, v_i_3531_, v_k_3532_);
    lean_dec(v_k_3532_);
    lean_dec_ref(v_vals_3529_);
    lean_dec_ref(v_keys_3528_);
    return v_res_3533_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_3534_: *mut LeanObject,
    mut v_n_3535_: *mut LeanObject,
    mut v_k_3536_: *mut LeanObject,
    mut v_v_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    v___x_3538_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6___redArg(v_n_3535_, v_k_3536_, v_v_3537_);
    return v___x_3538_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_3539_: *mut LeanObject,
    mut v_depth_3540_: usize,
    mut v_keys_3541_: *mut LeanObject,
    mut v_vals_3542_: *mut LeanObject,
    mut v_heq_3543_: *mut LeanObject,
    mut v_i_3544_: *mut LeanObject,
    mut v_entries_3545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    v___x_3546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_3540_, v_keys_3541_, v_vals_3542_, v_i_3544_, v_entries_3545_);
    return v___x_3546_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_3547_: *mut LeanObject,
    mut v_depth_3548_: *mut LeanObject,
    mut v_keys_3549_: *mut LeanObject,
    mut v_vals_3550_: *mut LeanObject,
    mut v_heq_3551_: *mut LeanObject,
    mut v_i_3552_: *mut LeanObject,
    mut v_entries_3553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3554_: usize = 0;
    let mut v_res_3555_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3554_ = lean_unbox_usize(v_depth_3548_);
    lean_dec(v_depth_3548_);
    v_res_3555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_3547_, v_depth_boxed_3554_, v_keys_3549_, v_vals_3550_, v_heq_3551_, v_i_3552_, v_entries_3553_);
    lean_dec_ref(v_vals_3550_);
    lean_dec_ref(v_keys_3549_);
    return v_res_3555_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(
    mut v_x_3556_: *mut LeanObject,
    mut v_keys_3557_: *mut LeanObject,
    mut v_v_3558_: *mut LeanObject,
    mut v_k_3559_: *mut LeanObject,
    mut v_as_3560_: *mut LeanObject,
    mut v_k_3561_: *mut LeanObject,
    mut v_x_3562_: *mut LeanObject,
    mut v_x_3563_: *mut LeanObject,
    mut v_x_3564_: *mut LeanObject,
    mut v_x_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    v___x_3566_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___redArg(v_x_3556_, v_keys_3557_, v_v_3558_, v_k_3559_, v_as_3560_, v_k_3561_, v_x_3562_, v_x_3563_);
    return v___x_3566_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_x_3567_: *mut LeanObject,
    mut v_keys_3568_: *mut LeanObject,
    mut v_v_3569_: *mut LeanObject,
    mut v_k_3570_: *mut LeanObject,
    mut v_as_3571_: *mut LeanObject,
    mut v_k_3572_: *mut LeanObject,
    mut v_x_3573_: *mut LeanObject,
    mut v_x_3574_: *mut LeanObject,
    mut v_x_3575_: *mut LeanObject,
    mut v_x_3576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3577_: *mut LeanObject = core::ptr::null_mut();
    v_res_3577_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__2_spec__6_spec__12(v_x_3567_, v_keys_3568_, v_v_3569_, v_k_3570_, v_as_3571_, v_k_3572_, v_x_3573_, v_x_3574_, v_x_3575_, v_x_3576_);
    lean_dec_ref(v_k_3572_);
    lean_dec_ref(v_keys_3568_);
    lean_dec(v_x_3567_);
    return v_res_3577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8(
    mut v_00_u03b2_3578_: *mut LeanObject,
    mut v_x_3579_: *mut LeanObject,
    mut v_x_3580_: *mut LeanObject,
    mut v_x_3581_: *mut LeanObject,
    mut v_x_3582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    v___x_3583_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_UnificationHints_add_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_3579_, v_x_3580_, v_x_3581_, v_x_3582_);
    return v___x_3583_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(
    mut v_x_3584_: *mut LeanObject,
    mut v_a_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    v___x_3586_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3586_, 0, v_a_3585_);
    lean_inc_ref_n(v___x_3586_, 2);
    v___x_3587_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3587_, 0, v___x_3586_);
    lean_ctor_set(v___x_3587_, 1, v___x_3586_);
    lean_ctor_set(v___x_3587_, 2, v___x_3586_);
    return v___x_3587_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(
    mut v_x_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3590_: *mut LeanObject = core::ptr::null_mut();
    v_res_3590_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v_x_3588_, v_a_3589_);
    lean_dec_ref(v_x_3588_);
    return v_res_3590_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(
    mut v___y_3591_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_3591_);
    return v___y_3591_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(
    mut v___y_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3593_: *mut LeanObject = core::ptr::null_mut();
    v_res_3593_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_(v___y_3592_);
    lean_dec_ref(v___y_3592_);
    return v_res_3593_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    v___f_3604_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_;
    v___f_3605_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_;
    v___x_3606_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedUnificationHints_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0,
    );
    v___x_3607_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_;
    v___x_3608_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_;
    v___x_3609_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3609_, 0, v___x_3608_);
    lean_ctor_set(v___x_3609_, 1, v___x_3607_);
    lean_ctor_set(v___x_3609_, 2, v___x_3606_);
    lean_ctor_set(v___x_3609_, 3, v___f_3605_);
    lean_ctor_set(v___x_3609_, 4, v___f_3604_);
    return v___x_3609_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    v___x_3611_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_);
    v___x_3612_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3611_);
    return v___x_3612_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2____boxed(
    mut v_a_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3614_: *mut LeanObject = core::ptr::null_mut();
    v_res_3614_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
    return v_res_3614_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3()
-> *mut LeanObject {
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    v___x_3619_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__2;
    v___x_3620_ = l_Lean_stringToMessageData(v___x_3619_);
    return v___x_3620_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(
    mut v_e_3621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: u8 = 0;
    v___x_3622_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__1;
    v___x_3623_ = lean_unsigned_to_nat(3);
    v___x_3624_ = l_Lean_Expr_isAppOfArity(v_e_3621_, v___x_3622_, v___x_3623_);
    if v___x_3624_ == 0 {
        let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
        v___x_3625_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint___closed__3);
        v___x_3626_ = l_Lean_indentExpr(v_e_3621_);
        v___x_3627_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_3627_, 0, v___x_3625_);
        lean_ctor_set(v___x_3627_, 1, v___x_3626_);
        v___x_3628_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3628_, 0, v___x_3627_);
        return v___x_3628_;
    } else {
        let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
        v___x_3629_ = l_Lean_Expr_appFn_x21(v_e_3621_);
        v___x_3630_ = l_Lean_Expr_appArg_x21(v___x_3629_);
        lean_dec_ref(v___x_3629_);
        v___x_3631_ = l_Lean_Expr_appArg_x21(v_e_3621_);
        lean_dec_ref(v_e_3621_);
        v___x_3632_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3632_, 0, v___x_3630_);
        lean_ctor_set(v___x_3632_, 1, v___x_3631_);
        v___x_3633_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3633_, 0, v___x_3632_);
        return v___x_3633_;
    }
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1()
-> *mut LeanObject {
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    v___x_3635_ =
        l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__0;
    v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
    return v___x_3636_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(
    mut v_e_3637_: *mut LeanObject,
    mut v_cs_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderType_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3645_: u8 = 0;
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_a_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3654_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3668_: u8 = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_a_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3637_) == 7 {
                    v_binderType_3639_ = lean_ctor_get(v_e_3637_, 1);
                    v_body_3640_ = lean_ctor_get(v_e_3637_, 2);
                    lean_inc_ref(v_binderType_3639_);
                    v___x_3641_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_binderType_3639_);
                    if lean_obj_tag(v___x_3641_) == 0 {
                        lean_dec_ref_known(v_e_3637_, 3);
                        lean_dec_ref(v_cs_3638_);
                        v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
                        v_isSharedCheck_3649_ = (!lean_is_exclusive(v___x_3641_)) as u8;
                        if v_isSharedCheck_3649_ == 0 {
                            v___x_3644_ = v___x_3641_;
                            v_isShared_3645_ = v_isSharedCheck_3649_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3642_);
                            lean_dec(v___x_3641_);
                            v___x_3644_ = lean_box(0);
                            v_isShared_3645_ = v_isSharedCheck_3649_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3650_ = lean_ctor_get(v___x_3641_, 0);
                        v_isSharedCheck_3663_ = (!lean_is_exclusive(v___x_3641_)) as u8;
                        if v_isSharedCheck_3663_ == 0 {
                            v___x_3652_ = v___x_3641_;
                            v_isShared_3653_ = v_isSharedCheck_3663_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3650_);
                            lean_dec(v___x_3641_);
                            v___x_3652_ = lean_box(0);
                            v_isShared_3653_ = v_isSharedCheck_3663_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3664_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decodeConstraint(v_e_3637_);
                    if lean_obj_tag(v___x_3664_) == 0 {
                        lean_dec_ref(v_cs_3638_);
                        v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
                        v_isSharedCheck_3672_ = (!lean_is_exclusive(v___x_3664_)) as u8;
                        if v_isSharedCheck_3672_ == 0 {
                            v___x_3667_ = v___x_3664_;
                            v_isShared_3668_ = v_isSharedCheck_3672_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3665_);
                            lean_dec(v___x_3664_);
                            v___x_3667_ = lean_box(0);
                            v_isShared_3668_ = v_isSharedCheck_3672_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_3673_ = lean_ctor_get(v___x_3664_, 0);
                        v_isSharedCheck_3682_ = (!lean_is_exclusive(v___x_3664_)) as u8;
                        if v_isSharedCheck_3682_ == 0 {
                            v___x_3675_ = v___x_3664_;
                            v_isShared_3676_ = v_isSharedCheck_3682_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3673_);
                            lean_dec(v___x_3664_);
                            v___x_3675_ = lean_box(0);
                            v_isShared_3676_ = v_isSharedCheck_3682_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3645_ == 0 {
                    v___x_3647_ = v___x_3644_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
                    v___x_3647_ = v_reuseFailAlloc_3648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3647_;
            }
            3 => {
                v___x_3654_ = l_Lean_Expr_hasLooseBVars(v_body_3640_);
                if v___x_3654_ == 0 {
                    lean_inc_ref(v_body_3640_);
                    lean_del_object(v___x_3652_);
                    lean_dec_ref_known(v_e_3637_, 3);
                    v___x_3655_ = lean_array_push(v_cs_3638_, v_a_3650_);
                    v_e_3637_ = v_body_3640_;
                    v_cs_3638_ = v___x_3655_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_3650_);
                    lean_dec_ref(v_cs_3638_);
                    v___x_3657_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode___closed__1);
                    v___x_3658_ = l_Lean_indentExpr(v_e_3637_);
                    v___x_3659_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3659_, 0, v___x_3657_);
                    lean_ctor_set(v___x_3659_, 1, v___x_3658_);
                    if v_isShared_3653_ == 0 {
                        lean_ctor_set_tag(v___x_3652_, 0);
                        lean_ctor_set(v___x_3652_, 0, v___x_3659_);
                        v___x_3661_ = v___x_3652_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
                        v___x_3661_ = v_reuseFailAlloc_3662_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3661_;
            }
            5 => {
                if v_isShared_3668_ == 0 {
                    v___x_3670_ = v___x_3667_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
                    v___x_3670_ = v_reuseFailAlloc_3671_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3670_;
            }
            7 => {
                v___x_3677_ = lean_array_to_list(v_cs_3638_);
                v___x_3678_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3678_, 0, v_a_3673_);
                lean_ctor_set(v___x_3678_, 1, v___x_3677_);
                if v_isShared_3676_ == 0 {
                    lean_ctor_set(v___x_3675_, 0, v___x_3678_);
                    v___x_3680_ = v___x_3675_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
                    v___x_3680_ = v_reuseFailAlloc_3681_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(
    mut v_e_3685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v___x_3686_ =
        l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint___closed__0;
    v___x_3687_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint_decode(
        v_e_3685_,
        v___x_3686_,
    );
    return v___x_3687_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(
    mut v_msgData_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    v___x_3694_ = lean_st_ref_get(v___y_3692_);
    v_env_3695_ = lean_ctor_get(v___x_3694_, 0);
    lean_inc_ref(v_env_3695_);
    lean_dec(v___x_3694_);
    v___x_3696_ = lean_st_ref_get(v___y_3690_);
    v_mctx_3697_ = lean_ctor_get(v___x_3696_, 0);
    lean_inc_ref(v_mctx_3697_);
    lean_dec(v___x_3696_);
    v_lctx_3698_ = lean_ctor_get(v___y_3689_, 2);
    v_options_3699_ = lean_ctor_get(v___y_3691_, 2);
    lean_inc_ref(v_options_3699_);
    lean_inc_ref(v_lctx_3698_);
    v___x_3700_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3700_, 0, v_env_3695_);
    lean_ctor_set(v___x_3700_, 1, v_mctx_3697_);
    lean_ctor_set(v___x_3700_, 2, v_lctx_3698_);
    lean_ctor_set(v___x_3700_, 3, v_options_3699_);
    v___x_3701_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3701_, 0, v___x_3700_);
    lean_ctor_set(v___x_3701_, 1, v_msgData_3688_);
    v___x_3702_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3702_, 0, v___x_3701_);
    return v___x_3702_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0___boxed(
    mut v_msgData_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3709_: *mut LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msgData_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
    lean_dec(v___y_3707_);
    lean_dec_ref(v___y_3706_);
    lean_dec(v___y_3705_);
    lean_dec_ref(v___y_3704_);
    return v_res_3709_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(
    mut v_msg_3710_: *mut LeanObject,
    mut v___y_3711_: *mut LeanObject,
    mut v___y_3712_: *mut LeanObject,
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3721_: u8 = 0;
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3716_ = lean_ctor_get(v___y_3713_, 5);
                v___x_3717_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
                v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
                v_isSharedCheck_3726_ = (!lean_is_exclusive(v___x_3717_)) as u8;
                if v_isSharedCheck_3726_ == 0 {
                    v___x_3720_ = v___x_3717_;
                    v_isShared_3721_ = v_isSharedCheck_3726_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3718_);
                    lean_dec(v___x_3717_);
                    v___x_3720_ = lean_box(0);
                    v_isShared_3721_ = v_isSharedCheck_3726_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3716_);
                v___x_3722_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3722_, 0, v_ref_3716_);
                lean_ctor_set(v___x_3722_, 1, v_a_3718_);
                if v_isShared_3721_ == 0 {
                    lean_ctor_set_tag(v___x_3720_, 1);
                    lean_ctor_set(v___x_3720_, 0, v___x_3722_);
                    v___x_3724_ = v___x_3720_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
                    v___x_3724_ = v_reuseFailAlloc_3725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg___boxed(
    mut v_msg_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
    mut v___y_3729_: *mut LeanObject,
    mut v___y_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3733_: *mut LeanObject = core::ptr::null_mut();
    v_res_3733_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
    lean_dec(v___y_3731_);
    lean_dec_ref(v___y_3730_);
    lean_dec(v___y_3729_);
    lean_dec_ref(v___y_3728_);
    return v_res_3733_;
}
pub unsafe fn _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__0;
    v___x_3736_ = l_Lean_stringToMessageData(v___x_3735_);
    return v___x_3736_;
}
pub unsafe fn _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    v___x_3738_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__2;
    v___x_3739_ = l_Lean_stringToMessageData(v___x_3738_);
    return v___x_3739_;
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(
    mut v_as_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
    mut v___y_3744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v_lhs_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_3740_) == 0 {
                    v___x_3746_ = lean_box(0);
                    v___x_3747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3747_, 0, v___x_3746_);
                    return v___x_3747_;
                } else {
                    v_head_3748_ = lean_ctor_get(v_as_3740_, 0);
                    v_tail_3749_ = lean_ctor_get(v_as_3740_, 1);
                    v_isSharedCheck_3783_ = (!lean_is_exclusive(v_as_3740_)) as u8;
                    if v_isSharedCheck_3783_ == 0 {
                        v___x_3751_ = v_as_3740_;
                        v_isShared_3752_ = v_isSharedCheck_3783_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3749_);
                        lean_inc(v_head_3748_);
                        lean_dec(v_as_3740_);
                        v___x_3751_ = lean_box(0);
                        v_isShared_3752_ = v_isSharedCheck_3783_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lhs_3753_ = lean_ctor_get(v_head_3748_, 0);
                v_rhs_3754_ = lean_ctor_get(v_head_3748_, 1);
                v_isSharedCheck_3782_ = (!lean_is_exclusive(v_head_3748_)) as u8;
                if v_isSharedCheck_3782_ == 0 {
                    v___x_3756_ = v_head_3748_;
                    v_isShared_3757_ = v_isSharedCheck_3782_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_rhs_3754_);
                    lean_inc(v_lhs_3753_);
                    lean_dec(v_head_3748_);
                    v___x_3756_ = lean_box(0);
                    v_isShared_3757_ = v_isSharedCheck_3782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_rhs_3754_);
                lean_inc_ref(v_lhs_3753_);
                v___x_3758_ = l_Lean_Meta_isExprDefEq(
                    v_lhs_3753_,
                    v_rhs_3754_,
                    v___y_3741_,
                    v___y_3742_,
                    v___y_3743_,
                    v___y_3744_,
                );
                if lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
                    lean_inc(v_a_3759_);
                    lean_dec_ref_known(v___x_3758_, 1);
                    v___x_3760_ = (lean_unbox(v_a_3759_) as u8);
                    lean_dec(v_a_3759_);
                    if v___x_3760_ == 0 {
                        lean_dec(v_tail_3749_);
                        v___x_3761_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1), core::ptr::addr_of_mut!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1_once), _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__1);
                        v___x_3762_ = l_Lean_indentExpr(v_lhs_3753_);
                        if v_isShared_3757_ == 0 {
                            lean_ctor_set_tag(v___x_3756_, 7);
                            lean_ctor_set(v___x_3756_, 1, v___x_3762_);
                            lean_ctor_set(v___x_3756_, 0, v___x_3761_);
                            v___x_3764_ = v___x_3756_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3772_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3761_);
                            lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3762_);
                            v___x_3764_ = v_reuseFailAlloc_3772_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3756_);
                        lean_dec_ref(v_rhs_3754_);
                        lean_dec_ref(v_lhs_3753_);
                        lean_del_object(v___x_3751_);
                        v_as_3740_ = v_tail_3749_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3756_);
                    lean_dec_ref(v_rhs_3754_);
                    lean_dec_ref(v_lhs_3753_);
                    lean_del_object(v___x_3751_);
                    lean_dec(v_tail_3749_);
                    v_a_3774_ = lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3781_ = (!lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3781_ == 0 {
                        v___x_3776_ = v___x_3758_;
                        v_isShared_3777_ = v_isSharedCheck_3781_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3774_);
                        lean_dec(v___x_3758_);
                        v___x_3776_ = lean_box(0);
                        v_isShared_3777_ = v_isSharedCheck_3781_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3765_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3), core::ptr::addr_of_mut!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once), _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
                if v_isShared_3752_ == 0 {
                    lean_ctor_set_tag(v___x_3751_, 7);
                    lean_ctor_set(v___x_3751_, 1, v___x_3765_);
                    lean_ctor_set(v___x_3751_, 0, v___x_3764_);
                    v___x_3767_ = v___x_3751_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3771_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3764_);
                    lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3765_);
                    v___x_3767_ = v_reuseFailAlloc_3771_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3768_ = l_Lean_indentExpr(v_rhs_3754_);
                v___x_3769_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3769_, 0, v___x_3767_);
                lean_ctor_set(v___x_3769_, 1, v___x_3768_);
                v___x_3770_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_3769_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
                return v___x_3770_;
            }
            5 => {
                if v_isShared_3777_ == 0 {
                    v___x_3779_ = v___x_3776_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
                    v___x_3779_ = v_reuseFailAlloc_3780_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___boxed(
    mut v_as_3784_: *mut LeanObject,
    mut v___y_3785_: *mut LeanObject,
    mut v___y_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
    mut v___y_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3790_: *mut LeanObject = core::ptr::null_mut();
    v_res_3790_ =
        l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(
            v_as_3784_,
            v___y_3785_,
            v___y_3786_,
            v___y_3787_,
            v___y_3788_,
        );
    lean_dec(v___y_3788_);
    lean_dec_ref(v___y_3787_);
    lean_dec(v___y_3786_);
    lean_dec_ref(v___y_3785_);
    return v_res_3790_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1()
-> *mut LeanObject {
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    v___x_3792_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__0;
    v___x_3793_ = l_Lean_stringToMessageData(v___x_3792_);
    return v___x_3793_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(
    mut v_hint_3794_: *mut LeanObject,
    mut v_a_3795_: *mut LeanObject,
    mut v_a_3796_: *mut LeanObject,
    mut v_a_3797_: *mut LeanObject,
    mut v_a_3798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pattern_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constraints_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3815_: u8 = 0;
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_a_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3837_: u8 = 0;
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pattern_3800_ = lean_ctor_get(v_hint_3794_, 0);
                v_constraints_3801_ = lean_ctor_get(v_hint_3794_, 1);
                v_isSharedCheck_3843_ = (!lean_is_exclusive(v_hint_3794_)) as u8;
                if v_isSharedCheck_3843_ == 0 {
                    v___x_3803_ = v_hint_3794_;
                    v_isShared_3804_ = v_isSharedCheck_3843_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_constraints_3801_);
                    lean_inc(v_pattern_3800_);
                    lean_dec(v_hint_3794_);
                    v___x_3803_ = lean_box(0);
                    v_isShared_3804_ = v_isSharedCheck_3843_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3805_ = l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1(v_constraints_3801_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_);
                if lean_obj_tag(v___x_3805_) == 0 {
                    lean_dec_ref_known(v___x_3805_, 1);
                    v_lhs_3806_ = lean_ctor_get(v_pattern_3800_, 0);
                    v_rhs_3807_ = lean_ctor_get(v_pattern_3800_, 1);
                    v_isSharedCheck_3842_ = (!lean_is_exclusive(v_pattern_3800_)) as u8;
                    if v_isSharedCheck_3842_ == 0 {
                        v___x_3809_ = v_pattern_3800_;
                        v_isShared_3810_ = v_isSharedCheck_3842_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_rhs_3807_);
                        lean_inc(v_lhs_3806_);
                        lean_dec(v_pattern_3800_);
                        v___x_3809_ = lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3842_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3803_);
                    lean_dec_ref(v_pattern_3800_);
                    return v___x_3805_;
                }
            }
            2 => {
                lean_inc_ref(v_rhs_3807_);
                lean_inc_ref(v_lhs_3806_);
                v___x_3811_ = l_Lean_Meta_isExprDefEq(
                    v_lhs_3806_,
                    v_rhs_3807_,
                    v_a_3795_,
                    v_a_3796_,
                    v_a_3797_,
                    v_a_3798_,
                );
                if lean_obj_tag(v___x_3811_) == 0 {
                    v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
                    v_isSharedCheck_3833_ = (!lean_is_exclusive(v___x_3811_)) as u8;
                    if v_isSharedCheck_3833_ == 0 {
                        v___x_3814_ = v___x_3811_;
                        v_isShared_3815_ = v_isSharedCheck_3833_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3812_);
                        lean_dec(v___x_3811_);
                        v___x_3814_ = lean_box(0);
                        v_isShared_3815_ = v_isSharedCheck_3833_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3809_);
                    lean_dec_ref(v_rhs_3807_);
                    lean_dec_ref(v_lhs_3806_);
                    lean_del_object(v___x_3803_);
                    v_a_3834_ = lean_ctor_get(v___x_3811_, 0);
                    v_isSharedCheck_3841_ = (!lean_is_exclusive(v___x_3811_)) as u8;
                    if v_isSharedCheck_3841_ == 0 {
                        v___x_3836_ = v___x_3811_;
                        v_isShared_3837_ = v_isSharedCheck_3841_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3834_);
                        lean_dec(v___x_3811_);
                        v___x_3836_ = lean_box(0);
                        v_isShared_3837_ = v_isSharedCheck_3841_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3816_ = (lean_unbox(v_a_3812_) as u8);
                lean_dec(v_a_3812_);
                if v___x_3816_ == 0 {
                    lean_del_object(v___x_3814_);
                    v___x_3817_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___closed__1);
                    v___x_3818_ = l_Lean_indentExpr(v_lhs_3806_);
                    if v_isShared_3810_ == 0 {
                        lean_ctor_set_tag(v___x_3809_, 7);
                        lean_ctor_set(v___x_3809_, 1, v___x_3818_);
                        lean_ctor_set(v___x_3809_, 0, v___x_3817_);
                        v___x_3820_ = v___x_3809_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3828_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3817_);
                        lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3818_);
                        v___x_3820_ = v_reuseFailAlloc_3828_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3809_);
                    lean_dec_ref(v_rhs_3807_);
                    lean_dec_ref(v_lhs_3806_);
                    lean_del_object(v___x_3803_);
                    v___x_3829_ = lean_box(0);
                    if v_isShared_3815_ == 0 {
                        lean_ctor_set(v___x_3814_, 0, v___x_3829_);
                        v___x_3831_ = v___x_3814_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
                        v___x_3831_ = v_reuseFailAlloc_3832_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3821_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3), core::ptr::addr_of_mut!(l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3_once), _init_l_List_forM___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__1___closed__3);
                if v_isShared_3804_ == 0 {
                    lean_ctor_set_tag(v___x_3803_, 7);
                    lean_ctor_set(v___x_3803_, 1, v___x_3821_);
                    lean_ctor_set(v___x_3803_, 0, v___x_3820_);
                    v___x_3823_ = v___x_3803_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3827_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3820_);
                    lean_ctor_set(v_reuseFailAlloc_3827_, 1, v___x_3821_);
                    v___x_3823_ = v_reuseFailAlloc_3827_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3824_ = l_Lean_indentExpr(v_rhs_3807_);
                v___x_3825_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3825_, 0, v___x_3823_);
                lean_ctor_set(v___x_3825_, 1, v___x_3824_);
                v___x_3826_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_3825_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_);
                return v___x_3826_;
            }
            6 => {
                return v___x_3831_;
            }
            7 => {
                if v_isShared_3837_ == 0 {
                    v___x_3839_ = v___x_3836_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
                    v___x_3839_ = v_reuseFailAlloc_3840_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint___boxed(
    mut v_hint_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
    mut v_a_3846_: *mut LeanObject,
    mut v_a_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
    mut v_a_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3850_: *mut LeanObject = core::ptr::null_mut();
    v_res_3850_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(
        v_hint_3844_,
        v_a_3845_,
        v_a_3846_,
        v_a_3847_,
        v_a_3848_,
    );
    lean_dec(v_a_3848_);
    lean_dec_ref(v_a_3847_);
    lean_dec(v_a_3846_);
    lean_dec_ref(v_a_3845_);
    return v_res_3850_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(
    mut v_00_u03b1_3851_: *mut LeanObject,
    mut v_msg_3852_: *mut LeanObject,
    mut v___y_3853_: *mut LeanObject,
    mut v___y_3854_: *mut LeanObject,
    mut v___y_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
    return v___x_3858_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___boxed(
    mut v_00_u03b1_3859_: *mut LeanObject,
    mut v_msg_3860_: *mut LeanObject,
    mut v___y_3861_: *mut LeanObject,
    mut v___y_3862_: *mut LeanObject,
    mut v___y_3863_: *mut LeanObject,
    mut v___y_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3866_: *mut LeanObject = core::ptr::null_mut();
    v_res_3866_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0(v_00_u03b1_3859_, v_msg_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
    lean_dec(v___y_3864_);
    lean_dec_ref(v___y_3863_);
    lean_dec(v___y_3862_);
    lean_dec_ref(v___y_3861_);
    return v_res_3866_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    v___x_3867_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3867_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    v___x_3868_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__0);
    v___x_3869_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3869_, 0, v___x_3868_);
    return v___x_3869_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    v___x_3870_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
    v___x_3871_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3871_, 0, v___x_3870_);
    lean_ctor_set(v___x_3871_, 1, v___x_3870_);
    return v___x_3871_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    v___x_3872_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__1);
    v___x_3873_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3873_, 0, v___x_3872_);
    lean_ctor_set(v___x_3873_, 1, v___x_3872_);
    lean_ctor_set(v___x_3873_, 2, v___x_3872_);
    lean_ctor_set(v___x_3873_, 3, v___x_3872_);
    lean_ctor_set(v___x_3873_, 4, v___x_3872_);
    lean_ctor_set(v___x_3873_, 5, v___x_3872_);
    return v___x_3873_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(
    mut v_ext_3874_: *mut LeanObject,
    mut v_b_3875_: *mut LeanObject,
    mut v_kind_3876_: u8,
    mut v___y_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
    mut v___y_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_unused_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3917_: u8 = 0;
    let mut v_unused_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_3881_ = lean_ctor_get(v___y_3878_, 6);
                v___x_3882_ = lean_st_ref_take(v___y_3879_);
                v_env_3883_ = lean_ctor_get(v___x_3882_, 0);
                v_nextMacroScope_3884_ = lean_ctor_get(v___x_3882_, 1);
                v_ngen_3885_ = lean_ctor_get(v___x_3882_, 2);
                v_auxDeclNGen_3886_ = lean_ctor_get(v___x_3882_, 3);
                v_traceState_3887_ = lean_ctor_get(v___x_3882_, 4);
                v_messages_3888_ = lean_ctor_get(v___x_3882_, 6);
                v_infoState_3889_ = lean_ctor_get(v___x_3882_, 7);
                v_snapshotTasks_3890_ = lean_ctor_get(v___x_3882_, 8);
                v_isSharedCheck_3917_ = (!lean_is_exclusive(v___x_3882_)) as u8;
                if v_isSharedCheck_3917_ == 0 {
                    v_unused_3918_ = lean_ctor_get(v___x_3882_, 5);
                    lean_dec(v_unused_3918_);
                    v___x_3892_ = v___x_3882_;
                    v_isShared_3893_ = v_isSharedCheck_3917_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3890_);
                    lean_inc(v_infoState_3889_);
                    lean_inc(v_messages_3888_);
                    lean_inc(v_traceState_3887_);
                    lean_inc(v_auxDeclNGen_3886_);
                    lean_inc(v_ngen_3885_);
                    lean_inc(v_nextMacroScope_3884_);
                    lean_inc(v_env_3883_);
                    lean_dec(v___x_3882_);
                    v___x_3892_ = lean_box(0);
                    v_isShared_3893_ = v_isSharedCheck_3917_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_3881_);
                v___x_3894_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_3883_,
                    v_ext_3874_,
                    v_b_3875_,
                    v_kind_3876_,
                    v_currNamespace_3881_,
                );
                v___x_3895_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__2);
                if v_isShared_3893_ == 0 {
                    lean_ctor_set(v___x_3892_, 5, v___x_3895_);
                    lean_ctor_set(v___x_3892_, 0, v___x_3894_);
                    v___x_3897_ = v___x_3892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3894_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_nextMacroScope_3884_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_ngen_3885_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 3, v_auxDeclNGen_3886_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 4, v_traceState_3887_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 5, v___x_3895_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 6, v_messages_3888_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 7, v_infoState_3889_);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 8, v_snapshotTasks_3890_);
                    v___x_3897_ = v_reuseFailAlloc_3916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3898_ = lean_st_ref_set(v___y_3879_, v___x_3897_);
                v___x_3899_ = lean_st_ref_take(v___y_3877_);
                v_mctx_3900_ = lean_ctor_get(v___x_3899_, 0);
                v_zetaDeltaFVarIds_3901_ = lean_ctor_get(v___x_3899_, 2);
                v_postponed_3902_ = lean_ctor_get(v___x_3899_, 3);
                v_diag_3903_ = lean_ctor_get(v___x_3899_, 4);
                v_isSharedCheck_3914_ = (!lean_is_exclusive(v___x_3899_)) as u8;
                if v_isSharedCheck_3914_ == 0 {
                    v_unused_3915_ = lean_ctor_get(v___x_3899_, 1);
                    lean_dec(v_unused_3915_);
                    v___x_3905_ = v___x_3899_;
                    v_isShared_3906_ = v_isSharedCheck_3914_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_3903_);
                    lean_inc(v_postponed_3902_);
                    lean_inc(v_zetaDeltaFVarIds_3901_);
                    lean_inc(v_mctx_3900_);
                    lean_dec(v___x_3899_);
                    v___x_3905_ = lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3914_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3907_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___closed__3);
                if v_isShared_3906_ == 0 {
                    lean_ctor_set(v___x_3905_, 1, v___x_3907_);
                    v___x_3909_ = v___x_3905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_mctx_3900_);
                    lean_ctor_set(v_reuseFailAlloc_3913_, 1, v___x_3907_);
                    lean_ctor_set(v_reuseFailAlloc_3913_, 2, v_zetaDeltaFVarIds_3901_);
                    lean_ctor_set(v_reuseFailAlloc_3913_, 3, v_postponed_3902_);
                    lean_ctor_set(v_reuseFailAlloc_3913_, 4, v_diag_3903_);
                    v___x_3909_ = v_reuseFailAlloc_3913_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3910_ = lean_st_ref_set(v___y_3877_, v___x_3909_);
                v___x_3911_ = lean_box(0);
                v___x_3912_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3912_, 0, v___x_3911_);
                return v___x_3912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg___boxed(
    mut v_ext_3919_: *mut LeanObject,
    mut v_b_3920_: *mut LeanObject,
    mut v_kind_3921_: *mut LeanObject,
    mut v___y_3922_: *mut LeanObject,
    mut v___y_3923_: *mut LeanObject,
    mut v___y_3924_: *mut LeanObject,
    mut v___y_3925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3926_: u8 = 0;
    let mut v_res_3927_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3926_ = (lean_unbox(v_kind_3921_) as u8);
    v_res_3927_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(
            v_ext_3919_,
            v_b_3920_,
            v_kind_boxed_3926_,
            v___y_3922_,
            v___y_3923_,
            v___y_3924_,
        );
    lean_dec(v___y_3924_);
    lean_dec_ref(v___y_3923_);
    lean_dec(v___y_3922_);
    return v_res_3927_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(
    mut v_00_u03b1_3928_: *mut LeanObject,
    mut v_00_u03b2_3929_: *mut LeanObject,
    mut v_00_u03c3_3930_: *mut LeanObject,
    mut v_ext_3931_: *mut LeanObject,
    mut v_b_3932_: *mut LeanObject,
    mut v_kind_3933_: u8,
    mut v___y_3934_: *mut LeanObject,
    mut v___y_3935_: *mut LeanObject,
    mut v___y_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    v___x_3939_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(
            v_ext_3931_,
            v_b_3932_,
            v_kind_3933_,
            v___y_3935_,
            v___y_3936_,
            v___y_3937_,
        );
    return v___x_3939_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___boxed(
    mut v_00_u03b1_3940_: *mut LeanObject,
    mut v_00_u03b2_3941_: *mut LeanObject,
    mut v_00_u03c3_3942_: *mut LeanObject,
    mut v_ext_3943_: *mut LeanObject,
    mut v_b_3944_: *mut LeanObject,
    mut v_kind_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
    mut v___y_3950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3951_: u8 = 0;
    let mut v_res_3952_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3951_ = (lean_unbox(v_kind_3945_) as u8);
    v_res_3952_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1(
        v_00_u03b1_3940_,
        v_00_u03b2_3941_,
        v_00_u03c3_3942_,
        v_ext_3943_,
        v_b_3944_,
        v_kind_boxed_3951_,
        v___y_3946_,
        v___y_3947_,
        v___y_3948_,
        v___y_3949_,
    );
    lean_dec(v___y_3949_);
    lean_dec_ref(v___y_3948_);
    lean_dec(v___y_3947_);
    lean_dec_ref(v___y_3946_);
    return v_res_3952_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(
    mut v_k_3953_: *mut LeanObject,
    mut v_allowLevelAssignments_3954_: u8,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
    mut v___y_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v_a_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3960_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_3954_,
                    v_k_3953_,
                    v___y_3955_,
                    v___y_3956_,
                    v___y_3957_,
                    v___y_3958_,
                );
                if lean_obj_tag(v___x_3960_) == 0 {
                    v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
                    v_isSharedCheck_3968_ = (!lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_3968_ == 0 {
                        v___x_3963_ = v___x_3960_;
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3961_);
                        lean_dec(v___x_3960_);
                        v___x_3963_ = lean_box(0);
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3969_ = lean_ctor_get(v___x_3960_, 0);
                    v_isSharedCheck_3976_ = (!lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_3976_ == 0 {
                        v___x_3971_ = v___x_3960_;
                        v_isShared_3972_ = v_isSharedCheck_3976_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3969_);
                        lean_dec(v___x_3960_);
                        v___x_3971_ = lean_box(0);
                        v_isShared_3972_ = v_isSharedCheck_3976_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3964_ == 0 {
                    v___x_3966_ = v___x_3963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3966_;
            }
            3 => {
                if v_isShared_3972_ == 0 {
                    v___x_3974_ = v___x_3971_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg___boxed(
    mut v_k_3977_: *mut LeanObject,
    mut v_allowLevelAssignments_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3984_: u8 = 0;
    let mut v_res_3985_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3984_ = (lean_unbox(v_allowLevelAssignments_3978_) as u8);
    v_res_3985_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(
            v_k_3977_,
            v_allowLevelAssignments_boxed_3984_,
            v___y_3979_,
            v___y_3980_,
            v___y_3981_,
            v___y_3982_,
        );
    lean_dec(v___y_3982_);
    lean_dec_ref(v___y_3981_);
    lean_dec(v___y_3980_);
    lean_dec_ref(v___y_3979_);
    return v_res_3985_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(
    mut v_00_u03b1_3986_: *mut LeanObject,
    mut v_k_3987_: *mut LeanObject,
    mut v_allowLevelAssignments_3988_: u8,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    v___x_3994_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(
            v_k_3987_,
            v_allowLevelAssignments_3988_,
            v___y_3989_,
            v___y_3990_,
            v___y_3991_,
            v___y_3992_,
        );
    return v___x_3994_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___boxed(
    mut v_00_u03b1_3995_: *mut LeanObject,
    mut v_k_3996_: *mut LeanObject,
    mut v_allowLevelAssignments_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
    mut v___y_3999_: *mut LeanObject,
    mut v___y_4000_: *mut LeanObject,
    mut v___y_4001_: *mut LeanObject,
    mut v___y_4002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_4003_: u8 = 0;
    let mut v_res_4004_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_4003_ = (lean_unbox(v_allowLevelAssignments_3997_) as u8);
    v_res_4004_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2(
        v_00_u03b1_3995_,
        v_k_3996_,
        v_allowLevelAssignments_boxed_4003_,
        v___y_3998_,
        v___y_3999_,
        v___y_4000_,
        v___y_4001_,
    );
    lean_dec(v___y_4001_);
    lean_dec_ref(v___y_4000_);
    lean_dec(v___y_3999_);
    lean_dec_ref(v___y_3998_);
    return v_res_4004_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    v___x_4005_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4005_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    v___x_4006_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
    v___x_4007_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4007_, 0, v___x_4006_);
    return v___x_4007_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    v___x_4008_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_4009_ = lean_unsigned_to_nat(0);
    v___x_4010_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4010_, 0, v___x_4009_);
    lean_ctor_set(v___x_4010_, 1, v___x_4009_);
    lean_ctor_set(v___x_4010_, 2, v___x_4009_);
    lean_ctor_set(v___x_4010_, 3, v___x_4009_);
    lean_ctor_set(v___x_4010_, 4, v___x_4008_);
    lean_ctor_set(v___x_4010_, 5, v___x_4008_);
    lean_ctor_set(v___x_4010_, 6, v___x_4008_);
    lean_ctor_set(v___x_4010_, 7, v___x_4008_);
    lean_ctor_set(v___x_4010_, 8, v___x_4008_);
    lean_ctor_set(v___x_4010_, 9, v___x_4008_);
    return v___x_4010_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    v___x_4011_ = lean_unsigned_to_nat(32);
    v___x_4012_ = lean_mk_empty_array_with_capacity(v___x_4011_);
    v___x_4013_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4013_, 0, v___x_4012_);
    return v___x_4013_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4014_: usize = 0;
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    v___x_4014_ = 5usize;
    v___x_4015_ = lean_unsigned_to_nat(0);
    v___x_4016_ = lean_unsigned_to_nat(32);
    v___x_4017_ = lean_mk_empty_array_with_capacity(v___x_4016_);
    v___x_4018_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
    v___x_4019_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4019_, 0, v___x_4018_);
    lean_ctor_set(v___x_4019_, 1, v___x_4017_);
    lean_ctor_set(v___x_4019_, 2, v___x_4015_);
    lean_ctor_set(v___x_4019_, 3, v___x_4015_);
    lean_ctor_set_usize(v___x_4019_, 4, v___x_4014_);
    return v___x_4019_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    v___x_4020_ = lean_box(1);
    v___x_4021_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_4022_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_4023_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4023_, 0, v___x_4022_);
    lean_ctor_set(v___x_4023_, 1, v___x_4021_);
    lean_ctor_set(v___x_4023_, 2, v___x_4020_);
    return v___x_4023_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    v___x_4025_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_4026_ = l_Lean_stringToMessageData(v___x_4025_);
    return v___x_4026_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    v___x_4028_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_4029_ = l_Lean_stringToMessageData(v___x_4028_);
    return v___x_4029_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    v___x_4031_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_4032_ = l_Lean_stringToMessageData(v___x_4031_);
    return v___x_4032_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    v___x_4034_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_4035_ = l_Lean_stringToMessageData(v___x_4034_);
    return v___x_4035_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__14;
    v___x_4038_ = l_Lean_stringToMessageData(v___x_4037_);
    return v___x_4038_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    v___x_4040_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__16;
    v___x_4041_ = l_Lean_stringToMessageData(v___x_4040_);
    return v___x_4041_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    v___x_4043_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__18;
    v___x_4044_ = l_Lean_stringToMessageData(v___x_4043_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(
    mut v_msg_4045_: *mut LeanObject,
    mut v_declHint_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: u8 = 0;
    let mut v_isExporting_4052_: u8 = 0;
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4074_: u8 = 0;
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4049_ = lean_st_ref_get(v___y_4047_);
                v_env_4050_ = lean_ctor_get(v___x_4049_, 0);
                lean_inc_ref(v_env_4050_);
                lean_dec(v___x_4049_);
                v___x_4051_ = l_Lean_Name_isAnonymous(v_declHint_4046_);
                if v___x_4051_ == 0 {
                    v_isExporting_4052_ = lean_ctor_get_uint8(
                        v_env_4050_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4052_ == 0 {
                        lean_dec_ref(v_env_4050_);
                        lean_dec(v_declHint_4046_);
                        v___x_4053_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4053_, 0, v_msg_4045_);
                        return v___x_4053_;
                    } else {
                        lean_inc_ref(v_env_4050_);
                        v___x_4054_ = l_Lean_Environment_setExporting(v_env_4050_, v___x_4051_);
                        lean_inc(v_declHint_4046_);
                        lean_inc_ref(v___x_4054_);
                        v___x_4055_ = l_Lean_Environment_contains(
                            v___x_4054_,
                            v_declHint_4046_,
                            v_isExporting_4052_,
                        );
                        if v___x_4055_ == 0 {
                            lean_dec_ref(v___x_4054_);
                            lean_dec_ref(v_env_4050_);
                            lean_dec(v_declHint_4046_);
                            v___x_4056_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4056_, 0, v_msg_4045_);
                            return v___x_4056_;
                        } else {
                            v___x_4057_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
                            v___x_4058_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
                            v___x_4059_ = l_Lean_Options_empty;
                            v___x_4060_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_4060_, 0, v___x_4054_);
                            lean_ctor_set(v___x_4060_, 1, v___x_4057_);
                            lean_ctor_set(v___x_4060_, 2, v___x_4058_);
                            lean_ctor_set(v___x_4060_, 3, v___x_4059_);
                            lean_inc(v_declHint_4046_);
                            v___x_4061_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4046_, v___x_4051_);
                            v_c_4062_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_4062_, 0, v___x_4060_);
                            lean_ctor_set(v_c_4062_, 1, v___x_4061_);
                            v___x_4063_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4050_,
                                v_declHint_4046_,
                            );
                            if lean_obj_tag(v___x_4063_) == 0 {
                                lean_dec_ref(v_env_4050_);
                                lean_dec(v_declHint_4046_);
                                v___x_4064_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
                                v___x_4065_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4065_, 0, v___x_4064_);
                                lean_ctor_set(v___x_4065_, 1, v_c_4062_);
                                v___x_4066_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
                                v___x_4067_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4067_, 0, v___x_4065_);
                                lean_ctor_set(v___x_4067_, 1, v___x_4066_);
                                v___x_4068_ = l_Lean_MessageData_note(v___x_4067_);
                                v___x_4069_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4069_, 0, v_msg_4045_);
                                lean_ctor_set(v___x_4069_, 1, v___x_4068_);
                                v___x_4070_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4070_, 0, v___x_4069_);
                                return v___x_4070_;
                            } else {
                                v_val_4071_ = lean_ctor_get(v___x_4063_, 0);
                                v_isSharedCheck_4106_ = (!lean_is_exclusive(v___x_4063_)) as u8;
                                if v_isSharedCheck_4106_ == 0 {
                                    v___x_4073_ = v___x_4063_;
                                    v_isShared_4074_ = v_isSharedCheck_4106_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_4071_);
                                    lean_dec(v___x_4063_);
                                    v___x_4073_ = lean_box(0);
                                    v_isShared_4074_ = v_isSharedCheck_4106_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_4050_);
                    lean_dec(v_declHint_4046_);
                    v___x_4107_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4107_, 0, v_msg_4045_);
                    return v___x_4107_;
                }
            }
            1 => {
                v___x_4075_ = lean_box(0);
                v___x_4076_ = l_Lean_Environment_header(v_env_4050_);
                lean_dec_ref(v_env_4050_);
                v___x_4077_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4076_);
                v_mod_4078_ = lean_array_get(v___x_4075_, v___x_4077_, v_val_4071_);
                lean_dec(v_val_4071_);
                lean_dec_ref(v___x_4077_);
                v___x_4079_ = l_Lean_isPrivateName(v_declHint_4046_);
                lean_dec(v_declHint_4046_);
                if v___x_4079_ == 0 {
                    v___x_4080_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_4081_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4081_, 0, v___x_4080_);
                    lean_ctor_set(v___x_4081_, 1, v_c_4062_);
                    v___x_4082_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_4083_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4083_, 0, v___x_4081_);
                    lean_ctor_set(v___x_4083_, 1, v___x_4082_);
                    v___x_4084_ = l_Lean_MessageData_ofName(v_mod_4078_);
                    v___x_4085_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4085_, 0, v___x_4083_);
                    lean_ctor_set(v___x_4085_, 1, v___x_4084_);
                    v___x_4086_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
                    v___x_4087_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4087_, 0, v___x_4085_);
                    lean_ctor_set(v___x_4087_, 1, v___x_4086_);
                    v___x_4088_ = l_Lean_MessageData_note(v___x_4087_);
                    v___x_4089_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4089_, 0, v_msg_4045_);
                    lean_ctor_set(v___x_4089_, 1, v___x_4088_);
                    if v_isShared_4074_ == 0 {
                        lean_ctor_set_tag(v___x_4073_, 0);
                        lean_ctor_set(v___x_4073_, 0, v___x_4089_);
                        v___x_4091_ = v___x_4073_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4089_);
                        v___x_4091_ = v_reuseFailAlloc_4092_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4093_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_4094_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4094_, 0, v___x_4093_);
                    lean_ctor_set(v___x_4094_, 1, v_c_4062_);
                    v___x_4095_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
                    v___x_4096_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4096_, 0, v___x_4094_);
                    lean_ctor_set(v___x_4096_, 1, v___x_4095_);
                    v___x_4097_ = l_Lean_MessageData_ofName(v_mod_4078_);
                    v___x_4098_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4098_, 0, v___x_4096_);
                    lean_ctor_set(v___x_4098_, 1, v___x_4097_);
                    v___x_4099_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
                    v___x_4100_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4100_, 0, v___x_4098_);
                    lean_ctor_set(v___x_4100_, 1, v___x_4099_);
                    v___x_4101_ = l_Lean_MessageData_note(v___x_4100_);
                    v___x_4102_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4102_, 0, v_msg_4045_);
                    lean_ctor_set(v___x_4102_, 1, v___x_4101_);
                    if v_isShared_4074_ == 0 {
                        lean_ctor_set_tag(v___x_4073_, 0);
                        lean_ctor_set(v___x_4073_, 0, v___x_4102_);
                        v___x_4104_ = v___x_4073_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
                        v___x_4104_ = v_reuseFailAlloc_4105_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4091_;
            }
            3 => {
                return v___x_4104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_4108_: *mut LeanObject,
    mut v_declHint_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4112_: *mut LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_4108_, v_declHint_4109_, v___y_4110_);
    lean_dec(v___y_4110_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(
    mut v_msg_4113_: *mut LeanObject,
    mut v_declHint_4114_: *mut LeanObject,
    mut v___y_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4120_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_4113_, v_declHint_4114_, v___y_4118_);
                v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
                v_isSharedCheck_4130_ = (!lean_is_exclusive(v___x_4120_)) as u8;
                if v_isSharedCheck_4130_ == 0 {
                    v___x_4123_ = v___x_4120_;
                    v_isShared_4124_ = v_isSharedCheck_4130_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4121_);
                    lean_dec(v___x_4120_);
                    v___x_4123_ = lean_box(0);
                    v_isShared_4124_ = v_isSharedCheck_4130_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4125_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4126_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4126_, 0, v___x_4125_);
                lean_ctor_set(v___x_4126_, 1, v_a_4121_);
                if v_isShared_4124_ == 0 {
                    lean_ctor_set(v___x_4123_, 0, v___x_4126_);
                    v___x_4128_ = v___x_4123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4126_);
                    v___x_4128_ = v_reuseFailAlloc_4129_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5___boxed(
    mut v_msg_4131_: *mut LeanObject,
    mut v_declHint_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
    mut v___y_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4138_: *mut LeanObject = core::ptr::null_mut();
    v_res_4138_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_4131_, v_declHint_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
    lean_dec(v___y_4136_);
    lean_dec_ref(v___y_4135_);
    lean_dec(v___y_4134_);
    lean_dec_ref(v___y_4133_);
    return v_res_4138_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(
    mut v_ref_4139_: *mut LeanObject,
    mut v_msg_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4158_: u8 = 0;
    let mut v_cancelTk_x3f_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4160_: u8 = 0;
    let mut v_inheritedTraceOptions_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4146_ = lean_ctor_get(v___y_4143_, 0);
    v_fileMap_4147_ = lean_ctor_get(v___y_4143_, 1);
    v_options_4148_ = lean_ctor_get(v___y_4143_, 2);
    v_currRecDepth_4149_ = lean_ctor_get(v___y_4143_, 3);
    v_maxRecDepth_4150_ = lean_ctor_get(v___y_4143_, 4);
    v_ref_4151_ = lean_ctor_get(v___y_4143_, 5);
    v_currNamespace_4152_ = lean_ctor_get(v___y_4143_, 6);
    v_openDecls_4153_ = lean_ctor_get(v___y_4143_, 7);
    v_initHeartbeats_4154_ = lean_ctor_get(v___y_4143_, 8);
    v_maxHeartbeats_4155_ = lean_ctor_get(v___y_4143_, 9);
    v_quotContext_4156_ = lean_ctor_get(v___y_4143_, 10);
    v_currMacroScope_4157_ = lean_ctor_get(v___y_4143_, 11);
    v_diag_4158_ = lean_ctor_get_uint8(
        v___y_4143_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4159_ = lean_ctor_get(v___y_4143_, 12);
    v_suppressElabErrors_4160_ = lean_ctor_get_uint8(
        v___y_4143_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4161_ = lean_ctor_get(v___y_4143_, 13);
    v_ref_4162_ = l_Lean_replaceRef(v_ref_4139_, v_ref_4151_);
    lean_inc_ref(v_inheritedTraceOptions_4161_);
    lean_inc(v_cancelTk_x3f_4159_);
    lean_inc(v_currMacroScope_4157_);
    lean_inc(v_quotContext_4156_);
    lean_inc(v_maxHeartbeats_4155_);
    lean_inc(v_initHeartbeats_4154_);
    lean_inc(v_openDecls_4153_);
    lean_inc(v_currNamespace_4152_);
    lean_inc(v_maxRecDepth_4150_);
    lean_inc(v_currRecDepth_4149_);
    lean_inc_ref(v_options_4148_);
    lean_inc_ref(v_fileMap_4147_);
    lean_inc_ref(v_fileName_4146_);
    v___x_4163_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4163_, 0, v_fileName_4146_);
    lean_ctor_set(v___x_4163_, 1, v_fileMap_4147_);
    lean_ctor_set(v___x_4163_, 2, v_options_4148_);
    lean_ctor_set(v___x_4163_, 3, v_currRecDepth_4149_);
    lean_ctor_set(v___x_4163_, 4, v_maxRecDepth_4150_);
    lean_ctor_set(v___x_4163_, 5, v_ref_4162_);
    lean_ctor_set(v___x_4163_, 6, v_currNamespace_4152_);
    lean_ctor_set(v___x_4163_, 7, v_openDecls_4153_);
    lean_ctor_set(v___x_4163_, 8, v_initHeartbeats_4154_);
    lean_ctor_set(v___x_4163_, 9, v_maxHeartbeats_4155_);
    lean_ctor_set(v___x_4163_, 10, v_quotContext_4156_);
    lean_ctor_set(v___x_4163_, 11, v_currMacroScope_4157_);
    lean_ctor_set(v___x_4163_, 12, v_cancelTk_x3f_4159_);
    lean_ctor_set(v___x_4163_, 13, v_inheritedTraceOptions_4161_);
    lean_ctor_set_uint8(
        v___x_4163_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4158_,
    );
    lean_ctor_set_uint8(
        v___x_4163_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4160_,
    );
    v___x_4164_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_msg_4140_, v___y_4141_, v___y_4142_, v___x_4163_, v___y_4144_);
    lean_dec_ref_known(v___x_4163_, 14);
    return v___x_4164_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_ref_4165_: *mut LeanObject,
    mut v_msg_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4172_: *mut LeanObject = core::ptr::null_mut();
    v_res_4172_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_4165_, v_msg_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
    lean_dec(v___y_4170_);
    lean_dec_ref(v___y_4169_);
    lean_dec(v___y_4168_);
    lean_dec_ref(v___y_4167_);
    lean_dec(v_ref_4165_);
    return v_res_4172_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_ref_4173_: *mut LeanObject,
    mut v_msg_4174_: *mut LeanObject,
    mut v_declHint_4175_: *mut LeanObject,
    mut v___y_4176_: *mut LeanObject,
    mut v___y_4177_: *mut LeanObject,
    mut v___y_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    v___x_4181_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5(v_msg_4174_, v_declHint_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
    v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
    lean_inc(v_a_4182_);
    lean_dec_ref(v___x_4181_);
    v___x_4183_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_4173_, v_a_4182_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
    return v___x_4183_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_ref_4184_: *mut LeanObject,
    mut v_msg_4185_: *mut LeanObject,
    mut v_declHint_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4192_: *mut LeanObject = core::ptr::null_mut();
    v_res_4192_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_4184_, v_msg_4185_, v_declHint_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
    lean_dec(v___y_4190_);
    lean_dec_ref(v___y_4189_);
    lean_dec(v___y_4188_);
    lean_dec_ref(v___y_4187_);
    lean_dec(v_ref_4184_);
    return v_res_4192_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    v___x_4194_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__0;
    v___x_4195_ = l_Lean_stringToMessageData(v___x_4194_);
    return v___x_4195_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__2;
    v___x_4198_ = l_Lean_stringToMessageData(v___x_4197_);
    return v___x_4198_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(
    mut v_ref_4199_: *mut LeanObject,
    mut v_constName_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    v___x_4206_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__1);
    v___x_4207_ = 0;
    lean_inc(v_constName_4200_);
    v___x_4208_ = l_Lean_MessageData_ofConstName(v_constName_4200_, v___x_4207_);
    v___x_4209_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4209_, 0, v___x_4206_);
    lean_ctor_set(v___x_4209_, 1, v___x_4208_);
    v___x_4210_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___closed__3);
    v___x_4211_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4211_, 0, v___x_4209_);
    lean_ctor_set(v___x_4211_, 1, v___x_4210_);
    v___x_4212_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_4199_, v___x_4211_, v_constName_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_ref_4213_: *mut LeanObject,
    mut v_constName_4214_: *mut LeanObject,
    mut v___y_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4220_: *mut LeanObject = core::ptr::null_mut();
    v_res_4220_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_4213_, v_constName_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
    lean_dec(v___y_4218_);
    lean_dec_ref(v___y_4217_);
    lean_dec(v___y_4216_);
    lean_dec_ref(v___y_4215_);
    lean_dec(v_ref_4213_);
    return v_res_4220_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(
    mut v_constName_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4227_ = lean_ctor_get(v___y_4224_, 5);
    v___x_4228_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_4227_, v_constName_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
    return v___x_4228_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg___boxed(
    mut v_constName_4229_: *mut LeanObject,
    mut v___y_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
    mut v___y_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4235_: *mut LeanObject = core::ptr::null_mut();
    v_res_4235_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
    lean_dec(v___y_4233_);
    lean_dec_ref(v___y_4232_);
    lean_dec(v___y_4231_);
    lean_dec_ref(v___y_4230_);
    return v_res_4235_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(
    mut v_constName_4236_: *mut LeanObject,
    mut v___y_4237_: *mut LeanObject,
    mut v___y_4238_: *mut LeanObject,
    mut v___y_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: u8 = 0;
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4242_ = lean_st_ref_get(v___y_4240_);
                v_env_4243_ = lean_ctor_get(v___x_4242_, 0);
                lean_inc_ref(v_env_4243_);
                lean_dec(v___x_4242_);
                v___x_4244_ = 0;
                lean_inc(v_constName_4236_);
                v___x_4245_ =
                    l_Lean_Environment_find_x3f(v_env_4243_, v_constName_4236_, v___x_4244_);
                if lean_obj_tag(v___x_4245_) == 0 {
                    v___x_4246_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
                    return v___x_4246_;
                } else {
                    lean_dec(v_constName_4236_);
                    v_val_4247_ = lean_ctor_get(v___x_4245_, 0);
                    v_isSharedCheck_4254_ = (!lean_is_exclusive(v___x_4245_)) as u8;
                    if v_isSharedCheck_4254_ == 0 {
                        v___x_4249_ = v___x_4245_;
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4247_);
                        lean_dec(v___x_4245_);
                        v___x_4249_ = lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4250_ == 0 {
                    lean_ctor_set_tag(v___x_4249_, 0);
                    v___x_4252_ = v___x_4249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_val_4247_);
                    v___x_4252_ = v_reuseFailAlloc_4253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0___boxed(
    mut v_constName_4255_: *mut LeanObject,
    mut v___y_4256_: *mut LeanObject,
    mut v___y_4257_: *mut LeanObject,
    mut v___y_4258_: *mut LeanObject,
    mut v___y_4259_: *mut LeanObject,
    mut v___y_4260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4261_: *mut LeanObject = core::ptr::null_mut();
    v_res_4261_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(
        v_constName_4255_,
        v___y_4256_,
        v___y_4257_,
        v___y_4258_,
        v___y_4259_,
    );
    lean_dec(v___y_4259_);
    lean_dec_ref(v___y_4258_);
    lean_dec(v___y_4257_);
    lean_dec_ref(v___y_4256_);
    return v_res_4261_;
}
pub unsafe fn _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    v___x_4263_ = l_Lean_Meta_addUnificationHint___lam__0___closed__0;
    v___x_4264_ = l_Lean_stringToMessageData(v___x_4263_);
    return v___x_4264_;
}
pub unsafe fn l_Lean_Meta_addUnificationHint___lam__0(
    mut v_declName_4265_: *mut LeanObject,
    mut v_kind_4266_: u8,
    mut v___y_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pattern_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_4295_: u8 = 0;
    let mut v_zetaDeltaSet_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4302_: u8 = 0;
    let mut v_inTypeClassResolution_4303_: u8 = 0;
    let mut v_cacheInferType_4304_: u8 = 0;
    let mut v___x_4305_: u64 = 0;
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v_isSharedCheck_4324_: u8 = 0;
    let mut v_unused_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4333_: u8 = 0;
    let mut v_a_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4337_: u8 = 0;
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_4265_);
                v___x_4272_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(
                    v_declName_4265_,
                    v___y_4267_,
                    v___y_4268_,
                    v___y_4269_,
                    v___y_4270_,
                );
                if lean_obj_tag(v___x_4272_) == 0 {
                    v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
                    lean_inc(v_a_4273_);
                    lean_dec_ref_known(v___x_4272_, 1);
                    v___x_4274_ = 0;
                    v___x_4275_ = l_Lean_ConstantInfo_value_x3f(v_a_4273_, v___x_4274_);
                    if lean_obj_tag(v___x_4275_) == 0 {
                        lean_dec(v_declName_4265_);
                        v___x_4276_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_addUnificationHint___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_addUnificationHint___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Meta_addUnificationHint___lam__0___closed__1,
                        );
                        v___x_4277_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v___x_4276_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
                        return v___x_4277_;
                    } else {
                        v_val_4278_ = lean_ctor_get(v___x_4275_, 0);
                        lean_inc(v_val_4278_);
                        lean_dec_ref_known(v___x_4275_, 1);
                        v___x_4279_ = lean_box(0);
                        v___x_4280_ = l_Lean_Meta_lambdaMetaTelescope(
                            v_val_4278_,
                            v___x_4279_,
                            v___y_4267_,
                            v___y_4268_,
                            v___y_4269_,
                            v___y_4270_,
                        );
                        lean_dec(v_val_4278_);
                        if lean_obj_tag(v___x_4280_) == 0 {
                            v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
                            lean_inc(v_a_4281_);
                            lean_dec_ref_known(v___x_4280_, 1);
                            v_snd_4282_ = lean_ctor_get(v_a_4281_, 1);
                            lean_inc(v_snd_4282_);
                            lean_dec(v_a_4281_);
                            v_snd_4283_ = lean_ctor_get(v_snd_4282_, 1);
                            lean_inc(v_snd_4283_);
                            lean_dec(v_snd_4282_);
                            v___x_4284_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(v_snd_4283_);
                            if lean_obj_tag(v___x_4284_) == 0 {
                                lean_dec(v_declName_4265_);
                                v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
                                lean_inc(v_a_4285_);
                                lean_dec_ref_known(v___x_4284_, 1);
                                v___x_4286_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0___redArg(v_a_4285_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
                                return v___x_4286_;
                            } else {
                                v_a_4287_ = lean_ctor_get(v___x_4284_, 0);
                                lean_inc(v_a_4287_);
                                lean_dec_ref_known(v___x_4284_, 1);
                                v_pattern_4288_ = lean_ctor_get(v_a_4287_, 0);
                                lean_inc_ref(v_pattern_4288_);
                                v_lhs_4289_ = lean_ctor_get(v_pattern_4288_, 0);
                                v_isSharedCheck_4324_ = (!lean_is_exclusive(v_pattern_4288_)) as u8;
                                if v_isSharedCheck_4324_ == 0 {
                                    v_unused_4325_ = lean_ctor_get(v_pattern_4288_, 1);
                                    lean_dec(v_unused_4325_);
                                    v___x_4291_ = v_pattern_4288_;
                                    v_isShared_4292_ = v_isSharedCheck_4324_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_lhs_4289_);
                                    lean_dec(v_pattern_4288_);
                                    v___x_4291_ = lean_box(0);
                                    v_isShared_4292_ = v_isSharedCheck_4324_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_declName_4265_);
                            v_a_4326_ = lean_ctor_get(v___x_4280_, 0);
                            v_isSharedCheck_4333_ = (!lean_is_exclusive(v___x_4280_)) as u8;
                            if v_isSharedCheck_4333_ == 0 {
                                v___x_4328_ = v___x_4280_;
                                v_isShared_4329_ = v_isSharedCheck_4333_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4326_);
                                lean_dec(v___x_4280_);
                                v___x_4328_ = lean_box(0);
                                v_isShared_4329_ = v_isSharedCheck_4333_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_declName_4265_);
                    v_a_4334_ = lean_ctor_get(v___x_4272_, 0);
                    v_isSharedCheck_4341_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4341_ == 0 {
                        v___x_4336_ = v___x_4272_;
                        v_isShared_4337_ = v_isSharedCheck_4341_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4334_);
                        lean_dec(v___x_4272_);
                        v___x_4336_ = lean_box(0);
                        v_isShared_4337_ = v_isSharedCheck_4341_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4293_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
                v_config_4294_ = lean_ctor_get(v___x_4293_, 0);
                v_trackZetaDelta_4295_ = lean_ctor_get_uint8(
                    v___y_4267_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4296_ = lean_ctor_get(v___y_4267_, 1);
                v_lctx_4297_ = lean_ctor_get(v___y_4267_, 2);
                v_localInstances_4298_ = lean_ctor_get(v___y_4267_, 3);
                v_defEqCtx_x3f_4299_ = lean_ctor_get(v___y_4267_, 4);
                v_synthPendingDepth_4300_ = lean_ctor_get(v___y_4267_, 5);
                v_canUnfold_x3f_4301_ = lean_ctor_get(v___y_4267_, 6);
                v_univApprox_4302_ = lean_ctor_get_uint8(
                    v___y_4267_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4303_ = lean_ctor_get_uint8(
                    v___y_4267_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4304_ = lean_ctor_get_uint8(
                    v___y_4267_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_4305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_4294_);
                lean_inc_ref(v_config_4294_);
                v___x_4306_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4306_, 0, v_config_4294_);
                lean_ctor_set_uint64(
                    v___x_4306_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4305_,
                );
                lean_inc(v_canUnfold_x3f_4301_);
                lean_inc(v_synthPendingDepth_4300_);
                lean_inc(v_defEqCtx_x3f_4299_);
                lean_inc_ref(v_localInstances_4298_);
                lean_inc_ref(v_lctx_4297_);
                lean_inc(v_zetaDeltaSet_4296_);
                v___x_4307_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4307_, 0, v___x_4306_);
                lean_ctor_set(v___x_4307_, 1, v_zetaDeltaSet_4296_);
                lean_ctor_set(v___x_4307_, 2, v_lctx_4297_);
                lean_ctor_set(v___x_4307_, 3, v_localInstances_4298_);
                lean_ctor_set(v___x_4307_, 4, v_defEqCtx_x3f_4299_);
                lean_ctor_set(v___x_4307_, 5, v_synthPendingDepth_4300_);
                lean_ctor_set(v___x_4307_, 6, v_canUnfold_x3f_4301_);
                lean_ctor_set_uint8(
                    v___x_4307_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4295_,
                );
                lean_ctor_set_uint8(
                    v___x_4307_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4302_,
                );
                lean_ctor_set_uint8(
                    v___x_4307_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4303_,
                );
                lean_ctor_set_uint8(
                    v___x_4307_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4304_,
                );
                v___x_4308_ = l_Lean_Meta_DiscrTree_mkPath(
                    v_lhs_4289_,
                    v___x_4274_,
                    v___x_4307_,
                    v___y_4268_,
                    v___y_4269_,
                    v___y_4270_,
                );
                lean_dec_ref_known(v___x_4307_, 7);
                if lean_obj_tag(v___x_4308_) == 0 {
                    v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
                    lean_inc(v_a_4309_);
                    lean_dec_ref_known(v___x_4308_, 1);
                    v___x_4310_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint(
                        v_a_4287_,
                        v___y_4267_,
                        v___y_4268_,
                        v___y_4269_,
                        v___y_4270_,
                    );
                    if lean_obj_tag(v___x_4310_) == 0 {
                        lean_dec_ref_known(v___x_4310_, 1);
                        v___x_4311_ = l_Lean_Meta_unificationHintExtension;
                        if v_isShared_4292_ == 0 {
                            lean_ctor_set(v___x_4291_, 1, v_declName_4265_);
                            lean_ctor_set(v___x_4291_, 0, v_a_4309_);
                            v___x_4313_ = v___x_4291_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
                            lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_declName_4265_);
                            v___x_4313_ = v_reuseFailAlloc_4315_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4309_);
                        lean_del_object(v___x_4291_);
                        lean_dec(v_declName_4265_);
                        return v___x_4310_;
                    }
                } else {
                    lean_del_object(v___x_4291_);
                    lean_dec(v_a_4287_);
                    lean_dec(v_declName_4265_);
                    v_a_4316_ = lean_ctor_get(v___x_4308_, 0);
                    v_isSharedCheck_4323_ = (!lean_is_exclusive(v___x_4308_)) as u8;
                    if v_isSharedCheck_4323_ == 0 {
                        v___x_4318_ = v___x_4308_;
                        v_isShared_4319_ = v_isSharedCheck_4323_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4316_);
                        lean_dec(v___x_4308_);
                        v___x_4318_ = lean_box(0);
                        v_isShared_4319_ = v_isSharedCheck_4323_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4314_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addUnificationHint_spec__1___redArg(v___x_4311_, v___x_4313_, v_kind_4266_, v___y_4268_, v___y_4269_, v___y_4270_);
                return v___x_4314_;
            }
            3 => {
                if v_isShared_4319_ == 0 {
                    v___x_4321_ = v___x_4318_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
                    v___x_4321_ = v_reuseFailAlloc_4322_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4321_;
            }
            5 => {
                if v_isShared_4329_ == 0 {
                    v___x_4331_ = v___x_4328_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
                    v___x_4331_ = v_reuseFailAlloc_4332_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4331_;
            }
            7 => {
                if v_isShared_4337_ == 0 {
                    v___x_4339_ = v___x_4336_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
                    v___x_4339_ = v_reuseFailAlloc_4340_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_addUnificationHint___lam__0___boxed(
    mut v_declName_4342_: *mut LeanObject,
    mut v_kind_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4349_: u8 = 0;
    let mut v_res_4350_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4349_ = (lean_unbox(v_kind_4343_) as u8);
    v_res_4350_ = l_Lean_Meta_addUnificationHint___lam__0(
        v_declName_4342_,
        v_kind_boxed_4349_,
        v___y_4344_,
        v___y_4345_,
        v___y_4346_,
        v___y_4347_,
    );
    lean_dec(v___y_4347_);
    lean_dec_ref(v___y_4346_);
    lean_dec(v___y_4345_);
    lean_dec_ref(v___y_4344_);
    return v_res_4350_;
}
pub unsafe fn l_Lean_Meta_addUnificationHint(
    mut v_declName_4351_: *mut LeanObject,
    mut v_kind_4352_: u8,
    mut v_a_4353_: *mut LeanObject,
    mut v_a_4354_: *mut LeanObject,
    mut v_a_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    v___x_4358_ = lean_box((v_kind_4352_) as usize);
    v___f_4359_ = lean_alloc_closure(
        l_Lean_Meta_addUnificationHint___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_4359_, 0, v_declName_4351_);
    lean_closure_set(v___f_4359_, 1, v___x_4358_);
    v___x_4360_ = 0;
    v___x_4361_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_addUnificationHint_spec__2___redArg(
            v___f_4359_,
            v___x_4360_,
            v_a_4353_,
            v_a_4354_,
            v_a_4355_,
            v_a_4356_,
        );
    return v___x_4361_;
}
pub unsafe fn l_Lean_Meta_addUnificationHint___boxed(
    mut v_declName_4362_: *mut LeanObject,
    mut v_kind_4363_: *mut LeanObject,
    mut v_a_4364_: *mut LeanObject,
    mut v_a_4365_: *mut LeanObject,
    mut v_a_4366_: *mut LeanObject,
    mut v_a_4367_: *mut LeanObject,
    mut v_a_4368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4369_: u8 = 0;
    let mut v_res_4370_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4369_ = (lean_unbox(v_kind_4363_) as u8);
    v_res_4370_ = l_Lean_Meta_addUnificationHint(
        v_declName_4362_,
        v_kind_boxed_4369_,
        v_a_4364_,
        v_a_4365_,
        v_a_4366_,
        v_a_4367_,
    );
    lean_dec(v_a_4367_);
    lean_dec_ref(v_a_4366_);
    lean_dec(v_a_4365_);
    lean_dec_ref(v_a_4364_);
    return v_res_4370_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(
    mut v_00_u03b1_4371_: *mut LeanObject,
    mut v_constName_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    v___x_4378_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___redArg(v_constName_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
    return v___x_4378_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0___boxed(
    mut v_00_u03b1_4379_: *mut LeanObject,
    mut v_constName_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
    mut v___y_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4386_: *mut LeanObject = core::ptr::null_mut();
    v_res_4386_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0(v_00_u03b1_4379_, v_constName_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
    lean_dec(v___y_4384_);
    lean_dec_ref(v___y_4383_);
    lean_dec(v___y_4382_);
    lean_dec_ref(v___y_4381_);
    return v_res_4386_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(
    mut v_00_u03b1_4387_: *mut LeanObject,
    mut v_ref_4388_: *mut LeanObject,
    mut v_constName_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    v___x_4395_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___redArg(v_ref_4388_, v_constName_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
    return v___x_4395_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_4396_: *mut LeanObject,
    mut v_ref_4397_: *mut LeanObject,
    mut v_constName_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4404_: *mut LeanObject = core::ptr::null_mut();
    v_res_4404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3(v_00_u03b1_4396_, v_ref_4397_, v_constName_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
    lean_dec(v___y_4402_);
    lean_dec_ref(v___y_4401_);
    lean_dec(v___y_4400_);
    lean_dec_ref(v___y_4399_);
    lean_dec(v_ref_4397_);
    return v_res_4404_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b1_4405_: *mut LeanObject,
    mut v_ref_4406_: *mut LeanObject,
    mut v_msg_4407_: *mut LeanObject,
    mut v_declHint_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
    mut v___y_4412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    v___x_4414_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___redArg(v_ref_4406_, v_msg_4407_, v_declHint_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
    return v___x_4414_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b1_4415_: *mut LeanObject,
    mut v_ref_4416_: *mut LeanObject,
    mut v_msg_4417_: *mut LeanObject,
    mut v_declHint_4418_: *mut LeanObject,
    mut v___y_4419_: *mut LeanObject,
    mut v___y_4420_: *mut LeanObject,
    mut v___y_4421_: *mut LeanObject,
    mut v___y_4422_: *mut LeanObject,
    mut v___y_4423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4424_: *mut LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4(v_00_u03b1_4415_, v_ref_4416_, v_msg_4417_, v_declHint_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
    lean_dec(v___y_4422_);
    lean_dec_ref(v___y_4421_);
    lean_dec(v___y_4420_);
    lean_dec_ref(v___y_4419_);
    lean_dec(v_ref_4416_);
    return v_res_4424_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(
    mut v_msg_4425_: *mut LeanObject,
    mut v_declHint_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    v___x_4432_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_4425_, v_declHint_4426_, v___y_4430_);
    return v___x_4432_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___boxed(
    mut v_msg_4433_: *mut LeanObject,
    mut v_declHint_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4440_: *mut LeanObject = core::ptr::null_mut();
    v_res_4440_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6(v_msg_4433_, v_declHint_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
    lean_dec(v___y_4438_);
    lean_dec_ref(v___y_4437_);
    lean_dec(v___y_4436_);
    lean_dec_ref(v___y_4435_);
    return v_res_4440_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(
    mut v_00_u03b1_4441_: *mut LeanObject,
    mut v_ref_4442_: *mut LeanObject,
    mut v_msg_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    v___x_4449_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___redArg(v_ref_4442_, v_msg_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
    return v___x_4449_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b1_4450_: *mut LeanObject,
    mut v_ref_4451_: *mut LeanObject,
    mut v_msg_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4458_: *mut LeanObject = core::ptr::null_mut();
    v_res_4458_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__6(v_00_u03b1_4450_, v_ref_4451_, v_msg_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
    lean_dec(v___y_4456_);
    lean_dec_ref(v___y_4455_);
    lean_dec(v___y_4454_);
    lean_dec_ref(v___y_4453_);
    lean_dec(v_ref_4451_);
    return v_res_4458_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: u64 = 0;
    v___x_4465_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4466_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4465_);
    return v___x_4466_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4467_: u64 = 0;
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    v___x_4467_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4468_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4469_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_4469_, 0, v___x_4468_);
    lean_ctor_set_uint64(
        v___x_4469_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4467_,
    );
    return v___x_4469_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    v___x_4470_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4470_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    v___x_4471_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4472_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4472_, 0, v___x_4471_);
    return v___x_4472_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    v___x_4473_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4474_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4474_, 0, v___x_4473_);
    lean_ctor_set(v___x_4474_, 1, v___x_4473_);
    lean_ctor_set(v___x_4474_, 2, v___x_4473_);
    lean_ctor_set(v___x_4474_, 3, v___x_4473_);
    lean_ctor_set(v___x_4474_, 4, v___x_4473_);
    lean_ctor_set(v___x_4474_, 5, v___x_4473_);
    return v___x_4474_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    v___x_4475_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4476_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4476_, 0, v___x_4475_);
    lean_ctor_set(v___x_4476_, 1, v___x_4475_);
    lean_ctor_set(v___x_4476_, 2, v___x_4475_);
    lean_ctor_set(v___x_4476_, 3, v___x_4475_);
    lean_ctor_set(v___x_4476_, 4, v___x_4475_);
    return v___x_4476_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(
    mut v___x_4477_: *mut LeanObject,
    mut v___x_4478_: *mut LeanObject,
    mut v_declName_4479_: *mut LeanObject,
    mut v_stx_4480_: *mut LeanObject,
    mut v_kind_4481_: u8,
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: u8 = 0;
    let mut v___x_4487_: u8 = 0;
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: usize = 0;
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4508_: u8 = 0;
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_unused_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4485_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_4480_, v___y_4482_, v___y_4483_);
                if lean_obj_tag(v___x_4485_) == 0 {
                    lean_dec_ref_known(v___x_4485_, 1);
                    v___x_4486_ = 0;
                    v___x_4487_ = 1;
                    v___x_4488_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
                    v___x_4489_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
                    v___x_4490_ = lean_unsigned_to_nat(32);
                    v___x_4491_ = lean_mk_empty_array_with_capacity(v___x_4490_);
                    v___x_4492_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
                    v___x_4493_ = 5usize;
                    lean_inc_n(v___x_4477_, 6);
                    v___x_4494_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v___x_4494_, 0, v___x_4492_);
                    lean_ctor_set(v___x_4494_, 1, v___x_4491_);
                    lean_ctor_set(v___x_4494_, 2, v___x_4477_);
                    lean_ctor_set(v___x_4494_, 3, v___x_4477_);
                    lean_ctor_set_usize(v___x_4494_, 4, v___x_4493_);
                    v___x_4495_ = lean_box(1);
                    lean_inc_ref(v___x_4494_);
                    v___x_4496_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_4496_, 0, v___x_4489_);
                    lean_ctor_set(v___x_4496_, 1, v___x_4494_);
                    lean_ctor_set(v___x_4496_, 2, v___x_4495_);
                    v___x_4497_ = lean_mk_empty_array_with_capacity(v___x_4477_);
                    v___x_4498_ = lean_box(0);
                    lean_inc(v___x_4478_);
                    v___x_4499_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v___x_4499_, 0, v___x_4488_);
                    lean_ctor_set(v___x_4499_, 1, v___x_4478_);
                    lean_ctor_set(v___x_4499_, 2, v___x_4496_);
                    lean_ctor_set(v___x_4499_, 3, v___x_4497_);
                    lean_ctor_set(v___x_4499_, 4, v___x_4498_);
                    lean_ctor_set(v___x_4499_, 5, v___x_4477_);
                    lean_ctor_set(v___x_4499_, 6, v___x_4498_);
                    lean_ctor_set_uint8(
                        v___x_4499_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v___x_4486_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4499_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v___x_4486_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4499_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v___x_4486_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4499_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        v___x_4487_,
                    );
                    v___x_4500_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v___x_4500_, 0, v___x_4477_);
                    lean_ctor_set(v___x_4500_, 1, v___x_4477_);
                    lean_ctor_set(v___x_4500_, 2, v___x_4477_);
                    lean_ctor_set(v___x_4500_, 3, v___x_4477_);
                    lean_ctor_set(v___x_4500_, 4, v___x_4489_);
                    lean_ctor_set(v___x_4500_, 5, v___x_4489_);
                    lean_ctor_set(v___x_4500_, 6, v___x_4489_);
                    lean_ctor_set(v___x_4500_, 7, v___x_4489_);
                    lean_ctor_set(v___x_4500_, 8, v___x_4489_);
                    lean_ctor_set(v___x_4500_, 9, v___x_4489_);
                    v___x_4501_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
                    v___x_4502_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
                    v___x_4503_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_4503_, 0, v___x_4500_);
                    lean_ctor_set(v___x_4503_, 1, v___x_4501_);
                    lean_ctor_set(v___x_4503_, 2, v___x_4478_);
                    lean_ctor_set(v___x_4503_, 3, v___x_4494_);
                    lean_ctor_set(v___x_4503_, 4, v___x_4502_);
                    v___x_4504_ = lean_st_mk_ref(v___x_4503_);
                    v___x_4505_ = l_Lean_Meta_addUnificationHint(
                        v_declName_4479_,
                        v_kind_4481_,
                        v___x_4499_,
                        v___x_4504_,
                        v___y_4482_,
                        v___y_4483_,
                    );
                    lean_dec_ref_known(v___x_4499_, 7);
                    if lean_obj_tag(v___x_4505_) == 0 {
                        v_isSharedCheck_4514_ = (!lean_is_exclusive(v___x_4505_)) as u8;
                        if v_isSharedCheck_4514_ == 0 {
                            v_unused_4515_ = lean_ctor_get(v___x_4505_, 0);
                            lean_dec(v_unused_4515_);
                            v___x_4507_ = v___x_4505_;
                            v_isShared_4508_ = v_isSharedCheck_4514_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4505_);
                            v___x_4507_ = lean_box(0);
                            v_isShared_4508_ = v_isSharedCheck_4514_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4504_);
                        return v___x_4505_;
                    }
                } else {
                    lean_dec(v_declName_4479_);
                    lean_dec(v___x_4478_);
                    lean_dec(v___x_4477_);
                    return v___x_4485_;
                }
            }
            1 => {
                v___x_4509_ = lean_st_ref_get(v___x_4504_);
                lean_dec(v___x_4504_);
                lean_dec(v___x_4509_);
                v___x_4510_ = lean_box(0);
                if v_isShared_4508_ == 0 {
                    lean_ctor_set(v___x_4507_, 0, v___x_4510_);
                    v___x_4512_ = v___x_4507_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(
    mut v___x_4516_: *mut LeanObject,
    mut v___x_4517_: *mut LeanObject,
    mut v_declName_4518_: *mut LeanObject,
    mut v_stx_4519_: *mut LeanObject,
    mut v_kind_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
    mut v___y_4523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4524_: u8 = 0;
    let mut v_res_4525_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4524_ = (lean_unbox(v_kind_4520_) as u8);
    v_res_4525_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_4516_, v___x_4517_, v_declName_4518_, v_stx_4519_, v_kind_boxed_4524_, v___y_4521_, v___y_4522_);
    lean_dec(v___y_4522_);
    lean_dec_ref(v___y_4521_);
    return v_res_4525_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    v___x_4530_ = lean_st_ref_get(v___y_4528_);
    v_env_4531_ = lean_ctor_get(v___x_4530_, 0);
    lean_inc_ref(v_env_4531_);
    lean_dec(v___x_4530_);
    v_options_4532_ = lean_ctor_get(v___y_4527_, 2);
    v___x_4533_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
    v___x_4534_ = lean_unsigned_to_nat(32);
    v___x_4535_ = lean_mk_empty_array_with_capacity(v___x_4534_);
    lean_dec_ref(v___x_4535_);
    v___x_4536_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0_spec__0_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
    lean_inc_ref(v_options_4532_);
    v___x_4537_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4537_, 0, v_env_4531_);
    lean_ctor_set(v___x_4537_, 1, v___x_4533_);
    lean_ctor_set(v___x_4537_, 2, v___x_4536_);
    lean_ctor_set(v___x_4537_, 3, v_options_4532_);
    v___x_4538_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4538_, 0, v___x_4537_);
    lean_ctor_set(v___x_4538_, 1, v_msgData_4526_);
    v___x_4539_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4539_, 0, v___x_4538_);
    return v___x_4539_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4544_: *mut LeanObject = core::ptr::null_mut();
    v_res_4544_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msgData_4540_, v___y_4541_, v___y_4542_);
    lean_dec(v___y_4542_);
    lean_dec_ref(v___y_4541_);
    return v_res_4544_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4554_: u8 = 0;
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4549_ = lean_ctor_get(v___y_4546_, 5);
                v___x_4550_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0_spec__0(v_msg_4545_, v___y_4546_, v___y_4547_);
                v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
                v_isSharedCheck_4559_ = (!lean_is_exclusive(v___x_4550_)) as u8;
                if v_isSharedCheck_4559_ == 0 {
                    v___x_4553_ = v___x_4550_;
                    v_isShared_4554_ = v_isSharedCheck_4559_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4551_);
                    lean_dec(v___x_4550_);
                    v___x_4553_ = lean_box(0);
                    v_isShared_4554_ = v_isSharedCheck_4559_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4549_);
                v___x_4555_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4555_, 0, v_ref_4549_);
                lean_ctor_set(v___x_4555_, 1, v_a_4551_);
                if v_isShared_4554_ == 0 {
                    lean_ctor_set_tag(v___x_4553_, 1);
                    lean_ctor_set(v___x_4553_, 0, v___x_4555_);
                    v___x_4557_ = v___x_4553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
    mut v___y_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4564_: *mut LeanObject = core::ptr::null_mut();
    v_res_4564_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_4560_, v___y_4561_, v___y_4562_);
    lean_dec(v___y_4562_);
    lean_dec_ref(v___y_4561_);
    return v_res_4564_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    v___x_4566_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4567_ = l_Lean_stringToMessageData(v___x_4566_);
    return v___x_4567_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    v___x_4569_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4570_ = l_Lean_stringToMessageData(v___x_4569_);
    return v___x_4570_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(
    mut v___x_4571_: *mut LeanObject,
    mut v_decl_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    v___x_4576_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4577_ = l_Lean_MessageData_ofName(v___x_4571_);
    v___x_4578_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4578_, 0, v___x_4576_);
    lean_ctor_set(v___x_4578_, 1, v___x_4577_);
    v___x_4579_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4580_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4580_, 0, v___x_4578_);
    lean_ctor_set(v___x_4580_, 1, v___x_4579_);
    v___x_4581_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v___x_4580_, v___y_4573_, v___y_4574_);
    return v___x_4581_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(
    mut v___x_4582_: *mut LeanObject,
    mut v_decl_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4587_: *mut LeanObject = core::ptr::null_mut();
    v_res_4587_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_(v___x_4582_, v_decl_4583_, v___y_4584_, v___y_4585_);
    lean_dec(v___y_4585_);
    lean_dec_ref(v___y_4584_);
    lean_dec(v_decl_4583_);
    return v_res_4587_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    v___x_4631_ = lean_unsigned_to_nat(3033092106);
    v___x_4632_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4633_ = l_Lean_Name_num___override(v___x_4632_, v___x_4631_);
    return v___x_4633_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    v___x_4635_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4636_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4637_ = l_Lean_Name_str___override(v___x_4636_, v___x_4635_);
    return v___x_4637_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    v___x_4639_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4640_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4641_ = l_Lean_Name_str___override(v___x_4640_, v___x_4639_);
    return v___x_4641_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    v___x_4642_ = lean_unsigned_to_nat(2);
    v___x_4643_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4644_ = l_Lean_Name_num___override(v___x_4643_, v___x_4642_);
    return v___x_4644_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4651_: u8 = 0;
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    v___x_4651_ = 0;
    v___x_4652_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4653_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4654_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4655_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_4655_, 0, v___x_4654_);
    lean_ctor_set(v___x_4655_, 1, v___x_4653_);
    lean_ctor_set(v___x_4655_, 2, v___x_4652_);
    lean_ctor_set_uint8(
        v___x_4655_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4651_,
    );
    return v___x_4655_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    v___f_4656_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___f_4657_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_4658_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4659_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4659_, 0, v___x_4658_);
    lean_ctor_set(v___x_4659_, 1, v___f_4657_);
    lean_ctor_set(v___x_4659_, 2, v___f_4656_);
    return v___x_4659_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    v___x_4661_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_);
    v___x_4662_ = l_Lean_registerBuiltinAttribute(v___x_4661_);
    return v___x_4662_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2____boxed(
    mut v_a_4663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4664_: *mut LeanObject = core::ptr::null_mut();
    v_res_4664_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
    return v_res_4664_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_4665_: *mut LeanObject,
    mut v_msg_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
    mut v___y_4668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    v___x_4670_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___redArg(v_msg_4666_, v___y_4667_, v___y_4668_);
    return v___x_4670_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_4671_: *mut LeanObject,
    mut v_msg_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4676_: *mut LeanObject = core::ptr::null_mut();
    v_res_4676_ = l_Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2__spec__0(v_00_u03b1_4671_, v_msg_4672_, v___y_4673_, v___y_4674_);
    lean_dec(v___y_4674_);
    lean_dec_ref(v___y_4673_);
    return v_res_4676_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0()
-> u64 {
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: u64 = 0;
    v___x_4677_ = 2;
    v___x_4678_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4677_);
    return v___x_4678_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(
    mut v_p_4679_: *mut LeanObject,
    mut v_e_4680_: *mut LeanObject,
    mut v_a_4681_: *mut LeanObject,
    mut v_a_4682_: *mut LeanObject,
    mut v_a_4683_: *mut LeanObject,
    mut v_a_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4687_: u8 = 0;
    let mut v_ctxApprox_4688_: u8 = 0;
    let mut v_quasiPatternApprox_4689_: u8 = 0;
    let mut v_constApprox_4690_: u8 = 0;
    let mut v_isDefEqStuckEx_4691_: u8 = 0;
    let mut v_unificationHints_4692_: u8 = 0;
    let mut v_proofIrrelevance_4693_: u8 = 0;
    let mut v_assignSyntheticOpaque_4694_: u8 = 0;
    let mut v_offsetCnstrs_4695_: u8 = 0;
    let mut v_etaStruct_4696_: u8 = 0;
    let mut v_univApprox_4697_: u8 = 0;
    let mut v_iota_4698_: u8 = 0;
    let mut v_beta_4699_: u8 = 0;
    let mut v_proj_4700_: u8 = 0;
    let mut v_zeta_4701_: u8 = 0;
    let mut v_zetaDelta_4702_: u8 = 0;
    let mut v_zetaUnused_4703_: u8 = 0;
    let mut v_zetaHave_4704_: u8 = 0;
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4707_: u8 = 0;
    let mut v_trackZetaDelta_4708_: u8 = 0;
    let mut v_zetaDeltaSet_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4715_: u8 = 0;
    let mut v_inTypeClassResolution_4716_: u8 = 0;
    let mut v_cacheInferType_4717_: u8 = 0;
    let mut v___x_4718_: u8 = 0;
    let mut v_config_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: u64 = 0;
    let mut v___x_4722_: u64 = 0;
    let mut v___x_4723_: u64 = 0;
    let mut v___x_4724_: u64 = 0;
    let mut v___x_4725_: u64 = 0;
    let mut v_key_4726_: u64 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4686_ = l_Lean_Meta_Context_config(v_a_4681_);
                v_foApprox_4687_ = lean_ctor_get_uint8(v___x_4686_, 0 as u32);
                v_ctxApprox_4688_ = lean_ctor_get_uint8(v___x_4686_, 1 as u32);
                v_quasiPatternApprox_4689_ = lean_ctor_get_uint8(v___x_4686_, 2 as u32);
                v_constApprox_4690_ = lean_ctor_get_uint8(v___x_4686_, 3 as u32);
                v_isDefEqStuckEx_4691_ = lean_ctor_get_uint8(v___x_4686_, 4 as u32);
                v_unificationHints_4692_ = lean_ctor_get_uint8(v___x_4686_, 5 as u32);
                v_proofIrrelevance_4693_ = lean_ctor_get_uint8(v___x_4686_, 6 as u32);
                v_assignSyntheticOpaque_4694_ = lean_ctor_get_uint8(v___x_4686_, 7 as u32);
                v_offsetCnstrs_4695_ = lean_ctor_get_uint8(v___x_4686_, 8 as u32);
                v_etaStruct_4696_ = lean_ctor_get_uint8(v___x_4686_, 10 as u32);
                v_univApprox_4697_ = lean_ctor_get_uint8(v___x_4686_, 11 as u32);
                v_iota_4698_ = lean_ctor_get_uint8(v___x_4686_, 12 as u32);
                v_beta_4699_ = lean_ctor_get_uint8(v___x_4686_, 13 as u32);
                v_proj_4700_ = lean_ctor_get_uint8(v___x_4686_, 14 as u32);
                v_zeta_4701_ = lean_ctor_get_uint8(v___x_4686_, 15 as u32);
                v_zetaDelta_4702_ = lean_ctor_get_uint8(v___x_4686_, 16 as u32);
                v_zetaUnused_4703_ = lean_ctor_get_uint8(v___x_4686_, 17 as u32);
                v_zetaHave_4704_ = lean_ctor_get_uint8(v___x_4686_, 18 as u32);
                v_isSharedCheck_4731_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                if v_isSharedCheck_4731_ == 0 {
                    v___x_4706_ = v___x_4686_;
                    v_isShared_4707_ = v_isSharedCheck_4731_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_4686_);
                    v___x_4706_ = lean_box(0);
                    v_isShared_4707_ = v_isSharedCheck_4731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_4708_ = lean_ctor_get_uint8(
                    v_a_4681_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4709_ = lean_ctor_get(v_a_4681_, 1);
                v_lctx_4710_ = lean_ctor_get(v_a_4681_, 2);
                v_localInstances_4711_ = lean_ctor_get(v_a_4681_, 3);
                v_defEqCtx_x3f_4712_ = lean_ctor_get(v_a_4681_, 4);
                v_synthPendingDepth_4713_ = lean_ctor_get(v_a_4681_, 5);
                v_canUnfold_x3f_4714_ = lean_ctor_get(v_a_4681_, 6);
                v_univApprox_4715_ = lean_ctor_get_uint8(
                    v_a_4681_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4716_ = lean_ctor_get_uint8(
                    v_a_4681_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4717_ = lean_ctor_get_uint8(
                    v_a_4681_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_4718_ = 2;
                if v_isShared_4707_ == 0 {
                    v_config_4720_ = v___x_4706_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 0 as u32, v_foApprox_4687_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 1 as u32, v_ctxApprox_4688_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4730_,
                        2 as u32,
                        v_quasiPatternApprox_4689_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 3 as u32, v_constApprox_4690_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 4 as u32, v_isDefEqStuckEx_4691_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 5 as u32, v_unificationHints_4692_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 6 as u32, v_proofIrrelevance_4693_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4730_,
                        7 as u32,
                        v_assignSyntheticOpaque_4694_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 8 as u32, v_offsetCnstrs_4695_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 10 as u32, v_etaStruct_4696_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 11 as u32, v_univApprox_4697_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 12 as u32, v_iota_4698_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 13 as u32, v_beta_4699_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 14 as u32, v_proj_4700_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 15 as u32, v_zeta_4701_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 16 as u32, v_zetaDelta_4702_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 17 as u32, v_zetaUnused_4703_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_4730_, 18 as u32, v_zetaHave_4704_);
                    v_config_4720_ = v_reuseFailAlloc_4730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_4720_, 9 as u32, v___x_4718_);
                v___x_4721_ = l_Lean_Meta_Context_configKey(v_a_4681_);
                v___x_4722_ = 3u64;
                v___x_4723_ = lean_uint64_shift_right(v___x_4721_, v___x_4722_);
                v___x_4724_ = lean_uint64_shift_left(v___x_4723_, v___x_4722_);
                v___x_4725_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___closed__0);
                v_key_4726_ = lean_uint64_lor(v___x_4724_, v___x_4725_);
                v___x_4727_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_4727_, 0, v_config_4720_);
                lean_ctor_set_uint64(
                    v___x_4727_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_4726_,
                );
                lean_inc(v_canUnfold_x3f_4714_);
                lean_inc(v_synthPendingDepth_4713_);
                lean_inc(v_defEqCtx_x3f_4712_);
                lean_inc_ref(v_localInstances_4711_);
                lean_inc_ref(v_lctx_4710_);
                lean_inc(v_zetaDeltaSet_4709_);
                v___x_4728_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_4728_, 0, v___x_4727_);
                lean_ctor_set(v___x_4728_, 1, v_zetaDeltaSet_4709_);
                lean_ctor_set(v___x_4728_, 2, v_lctx_4710_);
                lean_ctor_set(v___x_4728_, 3, v_localInstances_4711_);
                lean_ctor_set(v___x_4728_, 4, v_defEqCtx_x3f_4712_);
                lean_ctor_set(v___x_4728_, 5, v_synthPendingDepth_4713_);
                lean_ctor_set(v___x_4728_, 6, v_canUnfold_x3f_4714_);
                lean_ctor_set_uint8(
                    v___x_4728_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4708_,
                );
                lean_ctor_set_uint8(
                    v___x_4728_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4715_,
                );
                lean_ctor_set_uint8(
                    v___x_4728_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4716_,
                );
                lean_ctor_set_uint8(
                    v___x_4728_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4717_,
                );
                lean_inc(v_a_4684_);
                lean_inc_ref(v_a_4683_);
                lean_inc(v_a_4682_);
                v___x_4729_ = lean_is_expr_def_eq(
                    v_p_4679_,
                    v_e_4680_,
                    v___x_4728_,
                    v_a_4682_,
                    v_a_4683_,
                    v_a_4684_,
                );
                return v___x_4729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern___boxed(
    mut v_p_4732_: *mut LeanObject,
    mut v_e_4733_: *mut LeanObject,
    mut v_a_4734_: *mut LeanObject,
    mut v_a_4735_: *mut LeanObject,
    mut v_a_4736_: *mut LeanObject,
    mut v_a_4737_: *mut LeanObject,
    mut v_a_4738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4739_: *mut LeanObject = core::ptr::null_mut();
    v_res_4739_ =
        l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(
            v_p_4732_, v_e_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_,
        );
    lean_dec(v_a_4737_);
    lean_dec_ref(v_a_4736_);
    lean_dec(v_a_4735_);
    lean_dec_ref(v_a_4734_);
    return v_res_4739_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(
    mut v_x_4740_: *mut LeanObject,
    mut v_x_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
    mut v___y_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4766_: u8 = 0;
    let mut v_isSharedCheck_4767_: u8 = 0;
    let mut v_unused_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4740_) == 0 {
                    v___x_4747_ = l_List_reverse___redArg(v_x_4741_);
                    v___x_4748_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4748_, 0, v___x_4747_);
                    return v___x_4748_;
                } else {
                    v_tail_4749_ = lean_ctor_get(v_x_4740_, 1);
                    v_isSharedCheck_4767_ = (!lean_is_exclusive(v_x_4740_)) as u8;
                    if v_isSharedCheck_4767_ == 0 {
                        v_unused_4768_ = lean_ctor_get(v_x_4740_, 0);
                        lean_dec(v_unused_4768_);
                        v___x_4751_ = v_x_4740_;
                        v_isShared_4752_ = v_isSharedCheck_4767_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4749_);
                        lean_dec(v_x_4740_);
                        v___x_4751_ = lean_box(0);
                        v_isShared_4752_ = v_isSharedCheck_4767_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4753_ = l_Lean_Meta_mkFreshLevelMVar(
                    v___y_4742_,
                    v___y_4743_,
                    v___y_4744_,
                    v___y_4745_,
                );
                if lean_obj_tag(v___x_4753_) == 0 {
                    v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
                    lean_inc(v_a_4754_);
                    lean_dec_ref_known(v___x_4753_, 1);
                    if v_isShared_4752_ == 0 {
                        lean_ctor_set(v___x_4751_, 1, v_x_4741_);
                        lean_ctor_set(v___x_4751_, 0, v_a_4754_);
                        v___x_4756_ = v___x_4751_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4754_);
                        lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_x_4741_);
                        v___x_4756_ = v_reuseFailAlloc_4758_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4751_);
                    lean_dec(v_tail_4749_);
                    lean_dec(v_x_4741_);
                    v_a_4759_ = lean_ctor_get(v___x_4753_, 0);
                    v_isSharedCheck_4766_ = (!lean_is_exclusive(v___x_4753_)) as u8;
                    if v_isSharedCheck_4766_ == 0 {
                        v___x_4761_ = v___x_4753_;
                        v_isShared_4762_ = v_isSharedCheck_4766_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4759_);
                        lean_dec(v___x_4753_);
                        v___x_4761_ = lean_box(0);
                        v_isShared_4762_ = v_isSharedCheck_4766_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4740_ = v_tail_4749_;
                v_x_4741_ = v___x_4756_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4762_ == 0 {
                    v___x_4764_ = v___x_4761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
                    v___x_4764_ = v_reuseFailAlloc_4765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0___boxed(
    mut v_x_4769_: *mut LeanObject,
    mut v_x_4770_: *mut LeanObject,
    mut v___y_4771_: *mut LeanObject,
    mut v___y_4772_: *mut LeanObject,
    mut v___y_4773_: *mut LeanObject,
    mut v___y_4774_: *mut LeanObject,
    mut v___y_4775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4776_: *mut LeanObject = core::ptr::null_mut();
    v_res_4776_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v_x_4769_, v_x_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
    lean_dec(v___y_4774_);
    lean_dec_ref(v___y_4773_);
    lean_dec(v___y_4772_);
    lean_dec_ref(v___y_4771_);
    return v_res_4776_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0()
-> f64 {
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: f64 = 0.0;
    v___x_4777_ = lean_unsigned_to_nat(0);
    v___x_4778_ = lean_float_of_nat(v___x_4777_);
    return v___x_4778_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(
    mut v_cls_4782_: *mut LeanObject,
    mut v_msg_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
    mut v___y_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
    mut v___y_4787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4794_: u8 = 0;
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4807_: u8 = 0;
    let mut v_tid_4808_: u64 = 0;
    let mut v_traces_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4812_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: f64 = 0.0;
    let mut v___x_4815_: u8 = 0;
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4833_: u8 = 0;
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut v_isSharedCheck_4835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4789_ = lean_ctor_get(v___y_4786_, 5);
                v___x_4790_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
                v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
                v_isSharedCheck_4835_ = (!lean_is_exclusive(v___x_4790_)) as u8;
                if v_isSharedCheck_4835_ == 0 {
                    v___x_4793_ = v___x_4790_;
                    v_isShared_4794_ = v_isSharedCheck_4835_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4791_);
                    lean_dec(v___x_4790_);
                    v___x_4793_ = lean_box(0);
                    v_isShared_4794_ = v_isSharedCheck_4835_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4795_ = lean_st_ref_take(v___y_4787_);
                v_traceState_4796_ = lean_ctor_get(v___x_4795_, 4);
                v_env_4797_ = lean_ctor_get(v___x_4795_, 0);
                v_nextMacroScope_4798_ = lean_ctor_get(v___x_4795_, 1);
                v_ngen_4799_ = lean_ctor_get(v___x_4795_, 2);
                v_auxDeclNGen_4800_ = lean_ctor_get(v___x_4795_, 3);
                v_cache_4801_ = lean_ctor_get(v___x_4795_, 5);
                v_messages_4802_ = lean_ctor_get(v___x_4795_, 6);
                v_infoState_4803_ = lean_ctor_get(v___x_4795_, 7);
                v_snapshotTasks_4804_ = lean_ctor_get(v___x_4795_, 8);
                v_isSharedCheck_4834_ = (!lean_is_exclusive(v___x_4795_)) as u8;
                if v_isSharedCheck_4834_ == 0 {
                    v___x_4806_ = v___x_4795_;
                    v_isShared_4807_ = v_isSharedCheck_4834_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4804_);
                    lean_inc(v_infoState_4803_);
                    lean_inc(v_messages_4802_);
                    lean_inc(v_cache_4801_);
                    lean_inc(v_traceState_4796_);
                    lean_inc(v_auxDeclNGen_4800_);
                    lean_inc(v_ngen_4799_);
                    lean_inc(v_nextMacroScope_4798_);
                    lean_inc(v_env_4797_);
                    lean_dec(v___x_4795_);
                    v___x_4806_ = lean_box(0);
                    v_isShared_4807_ = v_isSharedCheck_4834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4808_ = lean_ctor_get_uint64(
                    v_traceState_4796_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4809_ = lean_ctor_get(v_traceState_4796_, 0);
                v_isSharedCheck_4833_ = (!lean_is_exclusive(v_traceState_4796_)) as u8;
                if v_isSharedCheck_4833_ == 0 {
                    v___x_4811_ = v_traceState_4796_;
                    v_isShared_4812_ = v_isSharedCheck_4833_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4809_);
                    lean_dec(v_traceState_4796_);
                    v___x_4811_ = lean_box(0);
                    v_isShared_4812_ = v_isSharedCheck_4833_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4813_ = lean_box(0);
                v___x_4814_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
                v___x_4815_ = 0;
                v___x_4816_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1;
                v___x_4817_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4817_, 0, v_cls_4782_);
                lean_ctor_set(v___x_4817_, 1, v___x_4813_);
                lean_ctor_set(v___x_4817_, 2, v___x_4816_);
                lean_ctor_set_float(
                    v___x_4817_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4814_,
                );
                lean_ctor_set_float(
                    v___x_4817_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4814_,
                );
                lean_ctor_set_uint8(
                    v___x_4817_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4815_,
                );
                v___x_4818_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__2;
                v___x_4819_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4819_, 0, v___x_4817_);
                lean_ctor_set(v___x_4819_, 1, v_a_4791_);
                lean_ctor_set(v___x_4819_, 2, v___x_4818_);
                lean_inc(v_ref_4789_);
                v___x_4820_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4820_, 0, v_ref_4789_);
                lean_ctor_set(v___x_4820_, 1, v___x_4819_);
                v___x_4821_ = l_Lean_PersistentArray_push___redArg(v_traces_4809_, v___x_4820_);
                if v_isShared_4812_ == 0 {
                    lean_ctor_set(v___x_4811_, 0, v___x_4821_);
                    v___x_4823_ = v___x_4811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4821_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4832_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4808_,
                    );
                    v___x_4823_ = v_reuseFailAlloc_4832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4807_ == 0 {
                    lean_ctor_set(v___x_4806_, 4, v___x_4823_);
                    v___x_4825_ = v___x_4806_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_env_4797_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_nextMacroScope_4798_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 2, v_ngen_4799_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 3, v_auxDeclNGen_4800_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 4, v___x_4823_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 5, v_cache_4801_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 6, v_messages_4802_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 7, v_infoState_4803_);
                    lean_ctor_set(v_reuseFailAlloc_4831_, 8, v_snapshotTasks_4804_);
                    v___x_4825_ = v_reuseFailAlloc_4831_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4826_ = lean_st_ref_set(v___y_4787_, v___x_4825_);
                v___x_4827_ = lean_box(0);
                if v_isShared_4794_ == 0 {
                    lean_ctor_set(v___x_4793_, 0, v___x_4827_);
                    v___x_4829_ = v___x_4793_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
                    v___x_4829_ = v_reuseFailAlloc_4830_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___boxed(
    mut v_cls_4836_: *mut LeanObject,
    mut v_msg_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
    mut v___y_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4843_: *mut LeanObject = core::ptr::null_mut();
    v_res_4843_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_4836_, v_msg_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
    lean_dec(v___y_4841_);
    lean_dec_ref(v___y_4840_);
    lean_dec(v___y_4839_);
    lean_dec_ref(v___y_4838_);
    return v_res_4843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(
    mut v_as_4847_: *mut LeanObject,
    mut v_sz_4848_: usize,
    mut v_i_4849_: usize,
    mut v_b_4850_: *mut LeanObject,
    mut v___y_4851_: *mut LeanObject,
    mut v___y_4852_: *mut LeanObject,
    mut v___y_4853_: *mut LeanObject,
    mut v___y_4854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: usize = 0;
    let mut v___x_4861_: u8 = 0;
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v_array_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: u8 = 0;
    let mut v___x_4885_: u8 = 0;
    let mut v___x_4886_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4897_: u8 = 0;
    let mut v_a_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4903_: u8 = 0;
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v_a_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4919_: u8 = 0;
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4931_: u8 = 0;
    let mut v_a_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_a_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4947_: u8 = 0;
    let mut v_reuseFailAlloc_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_unused_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v_unused_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4861_ = lean_usize_dec_lt(v_i_4849_, v_sz_4848_);
                if v___x_4861_ == 0 {
                    v___x_4862_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4862_, 0, v_b_4850_);
                    return v___x_4862_;
                } else {
                    v_snd_4863_ = lean_ctor_get(v_b_4850_, 1);
                    v_isSharedCheck_4953_ = (!lean_is_exclusive(v_b_4850_)) as u8;
                    if v_isSharedCheck_4953_ == 0 {
                        v_unused_4954_ = lean_ctor_get(v_b_4850_, 0);
                        lean_dec(v_unused_4954_);
                        v___x_4865_ = v_b_4850_;
                        v_isShared_4866_ = v_isSharedCheck_4953_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4863_);
                        lean_dec(v_b_4850_);
                        v___x_4865_ = lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4953_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4858_ = 1usize;
                v___x_4859_ = lean_usize_add(v_i_4849_, v___x_4858_);
                v_i_4849_ = v___x_4859_;
                v_b_4850_ = v_a_4857_;
                state = 0;
                continue;
            }
            2 => {
                v_array_4867_ = lean_ctor_get(v_snd_4863_, 0);
                v_start_4868_ = lean_ctor_get(v_snd_4863_, 1);
                v_stop_4869_ = lean_ctor_get(v_snd_4863_, 2);
                v___x_4870_ = lean_box(0);
                v___x_4871_ = lean_nat_dec_lt(v_start_4868_, v_stop_4869_);
                if v___x_4871_ == 0 {
                    if v_isShared_4866_ == 0 {
                        lean_ctor_set(v___x_4865_, 0, v___x_4870_);
                        v___x_4873_ = v___x_4865_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4870_);
                        lean_ctor_set(v_reuseFailAlloc_4875_, 1, v_snd_4863_);
                        v___x_4873_ = v_reuseFailAlloc_4875_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_4869_);
                    lean_inc(v_start_4868_);
                    lean_inc_ref(v_array_4867_);
                    v_isSharedCheck_4949_ = (!lean_is_exclusive(v_snd_4863_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v_unused_4950_ = lean_ctor_get(v_snd_4863_, 2);
                        lean_dec(v_unused_4950_);
                        v_unused_4951_ = lean_ctor_get(v_snd_4863_, 1);
                        lean_dec(v_unused_4951_);
                        v_unused_4952_ = lean_ctor_get(v_snd_4863_, 0);
                        lean_dec(v_unused_4952_);
                        v___x_4877_ = v_snd_4863_;
                        v_isShared_4878_ = v_isSharedCheck_4949_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_snd_4863_);
                        v___x_4877_ = lean_box(0);
                        v_isShared_4878_ = v_isSharedCheck_4949_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4874_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4874_, 0, v___x_4873_);
                return v___x_4874_;
            }
            4 => {
                v___x_4879_ = lean_array_fget(v_array_4867_, v_start_4868_);
                v___x_4880_ = lean_unsigned_to_nat(1);
                v___x_4881_ = lean_nat_add(v_start_4868_, v___x_4880_);
                lean_dec(v_start_4868_);
                if v_isShared_4878_ == 0 {
                    lean_ctor_set(v___x_4877_, 1, v___x_4881_);
                    v___x_4883_ = v___x_4877_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_array_4867_);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 1, v___x_4881_);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 2, v_stop_4869_);
                    v___x_4883_ = v_reuseFailAlloc_4948_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4884_ = 3;
                v___x_4885_ = (lean_unbox(v___x_4879_) as u8);
                lean_dec(v___x_4879_);
                v___x_4886_ = l_Lean_instBEqBinderInfo_beq(v___x_4885_, v___x_4884_);
                if v___x_4886_ == 0 {
                    if v_isShared_4866_ == 0 {
                        lean_ctor_set(v___x_4865_, 1, v___x_4883_);
                        lean_ctor_set(v___x_4865_, 0, v___x_4870_);
                        v___x_4888_ = v___x_4865_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4870_);
                        lean_ctor_set(v_reuseFailAlloc_4889_, 1, v___x_4883_);
                        v___x_4888_ = v_reuseFailAlloc_4889_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_4890_ = lean_array_uget_borrowed(v_as_4847_, v_i_4849_);
                    lean_inc(v___y_4854_);
                    lean_inc_ref(v___y_4853_);
                    lean_inc(v___y_4852_);
                    lean_inc_ref(v___y_4851_);
                    lean_inc(v_a_4890_);
                    v___x_4891_ = lean_infer_type(
                        v_a_4890_,
                        v___y_4851_,
                        v___y_4852_,
                        v___y_4853_,
                        v___y_4854_,
                    );
                    if lean_obj_tag(v___x_4891_) == 0 {
                        v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
                        lean_inc(v_a_4892_);
                        lean_dec_ref_known(v___x_4891_, 1);
                        v___x_4893_ = l_Lean_Meta_trySynthInstance(
                            v_a_4892_,
                            v___x_4870_,
                            v___y_4851_,
                            v___y_4852_,
                            v___y_4853_,
                            v___y_4854_,
                        );
                        if lean_obj_tag(v___x_4893_) == 0 {
                            v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
                            v_isSharedCheck_4931_ = (!lean_is_exclusive(v___x_4893_)) as u8;
                            if v_isSharedCheck_4931_ == 0 {
                                v___x_4896_ = v___x_4893_;
                                v_isShared_4897_ = v_isSharedCheck_4931_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4894_);
                                lean_dec(v___x_4893_);
                                v___x_4896_ = lean_box(0);
                                v_isShared_4897_ = v_isSharedCheck_4931_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_4883_);
                            lean_del_object(v___x_4865_);
                            v_a_4932_ = lean_ctor_get(v___x_4893_, 0);
                            v_isSharedCheck_4939_ = (!lean_is_exclusive(v___x_4893_)) as u8;
                            if v_isSharedCheck_4939_ == 0 {
                                v___x_4934_ = v___x_4893_;
                                v_isShared_4935_ = v_isSharedCheck_4939_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_4932_);
                                lean_dec(v___x_4893_);
                                v___x_4934_ = lean_box(0);
                                v_isShared_4935_ = v_isSharedCheck_4939_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_4883_);
                        lean_del_object(v___x_4865_);
                        v_a_4940_ = lean_ctor_get(v___x_4891_, 0);
                        v_isSharedCheck_4947_ = (!lean_is_exclusive(v___x_4891_)) as u8;
                        if v_isSharedCheck_4947_ == 0 {
                            v___x_4942_ = v___x_4891_;
                            v_isShared_4943_ = v_isSharedCheck_4947_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_4940_);
                            lean_dec(v___x_4891_);
                            v___x_4942_ = lean_box(0);
                            v_isShared_4943_ = v_isSharedCheck_4947_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v_a_4857_ = v___x_4888_;
                state = 1;
                continue;
            }
            7 => {
                if lean_obj_tag(v_a_4894_) == 1 {
                    lean_del_object(v___x_4896_);
                    v_a_4898_ = lean_ctor_get(v_a_4894_, 0);
                    lean_inc(v_a_4898_);
                    lean_dec_ref_known(v_a_4894_, 1);
                    lean_inc(v_a_4890_);
                    v___x_4899_ = l_Lean_Meta_isExprDefEq(
                        v_a_4890_,
                        v_a_4898_,
                        v___y_4851_,
                        v___y_4852_,
                        v___y_4853_,
                        v___y_4854_,
                    );
                    if lean_obj_tag(v___x_4899_) == 0 {
                        v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
                        v_isSharedCheck_4915_ = (!lean_is_exclusive(v___x_4899_)) as u8;
                        if v_isSharedCheck_4915_ == 0 {
                            v___x_4902_ = v___x_4899_;
                            v_isShared_4903_ = v_isSharedCheck_4915_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4900_);
                            lean_dec(v___x_4899_);
                            v___x_4902_ = lean_box(0);
                            v_isShared_4903_ = v_isSharedCheck_4915_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4883_);
                        lean_del_object(v___x_4865_);
                        v_a_4916_ = lean_ctor_get(v___x_4899_, 0);
                        v_isSharedCheck_4923_ = (!lean_is_exclusive(v___x_4899_)) as u8;
                        if v_isSharedCheck_4923_ == 0 {
                            v___x_4918_ = v___x_4899_;
                            v_isShared_4919_ = v_isSharedCheck_4923_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_4916_);
                            lean_dec(v___x_4899_);
                            v___x_4918_ = lean_box(0);
                            v_isShared_4919_ = v_isSharedCheck_4923_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4894_);
                    v___x_4924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0;
                    if v_isShared_4866_ == 0 {
                        lean_ctor_set(v___x_4865_, 1, v___x_4883_);
                        lean_ctor_set(v___x_4865_, 0, v___x_4924_);
                        v___x_4926_ = v___x_4865_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4924_);
                        lean_ctor_set(v_reuseFailAlloc_4930_, 1, v___x_4883_);
                        v___x_4926_ = v_reuseFailAlloc_4930_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4904_ = (lean_unbox(v_a_4900_) as u8);
                lean_dec(v_a_4900_);
                if v___x_4904_ == 0 {
                    v___x_4905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___closed__0;
                    if v_isShared_4866_ == 0 {
                        lean_ctor_set(v___x_4865_, 1, v___x_4883_);
                        lean_ctor_set(v___x_4865_, 0, v___x_4905_);
                        v___x_4907_ = v___x_4865_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4905_);
                        lean_ctor_set(v_reuseFailAlloc_4911_, 1, v___x_4883_);
                        v___x_4907_ = v_reuseFailAlloc_4911_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4902_);
                    if v_isShared_4866_ == 0 {
                        lean_ctor_set(v___x_4865_, 1, v___x_4883_);
                        lean_ctor_set(v___x_4865_, 0, v___x_4870_);
                        v___x_4913_ = v___x_4865_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4870_);
                        lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___x_4883_);
                        v___x_4913_ = v_reuseFailAlloc_4914_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4903_ == 0 {
                    lean_ctor_set(v___x_4902_, 0, v___x_4907_);
                    v___x_4909_ = v___x_4902_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4907_);
                    v___x_4909_ = v_reuseFailAlloc_4910_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4909_;
            }
            11 => {
                v_a_4857_ = v___x_4913_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_4919_ == 0 {
                    v___x_4921_ = v___x_4918_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
                    v___x_4921_ = v_reuseFailAlloc_4922_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4921_;
            }
            14 => {
                if v_isShared_4897_ == 0 {
                    lean_ctor_set(v___x_4896_, 0, v___x_4926_);
                    v___x_4928_ = v___x_4896_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4926_);
                    v___x_4928_ = v_reuseFailAlloc_4929_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4928_;
            }
            16 => {
                if v_isShared_4935_ == 0 {
                    v___x_4937_ = v___x_4934_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
                    v___x_4937_ = v_reuseFailAlloc_4938_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4937_;
            }
            18 => {
                if v_isShared_4943_ == 0 {
                    v___x_4945_ = v___x_4942_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
                    v___x_4945_ = v_reuseFailAlloc_4946_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2___boxed(
    mut v_as_4955_: *mut LeanObject,
    mut v_sz_4956_: *mut LeanObject,
    mut v_i_4957_: *mut LeanObject,
    mut v_b_4958_: *mut LeanObject,
    mut v___y_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
    mut v___y_4961_: *mut LeanObject,
    mut v___y_4962_: *mut LeanObject,
    mut v___y_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4964_: usize = 0;
    let mut v_i_boxed_4965_: usize = 0;
    let mut v_res_4966_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4964_ = lean_unbox_usize(v_sz_4956_);
    lean_dec(v_sz_4956_);
    v_i_boxed_4965_ = lean_unbox_usize(v_i_4957_);
    lean_dec(v_i_4957_);
    v_res_4966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_as_4955_, v_sz_boxed_4964_, v_i_boxed_4965_, v_b_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
    lean_dec(v___y_4962_);
    lean_dec_ref(v___y_4961_);
    lean_dec(v___y_4960_);
    lean_dec_ref(v___y_4959_);
    lean_dec_ref(v_as_4955_);
    return v_res_4966_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(
    mut v_as_x27_4970_: *mut LeanObject,
    mut v_b_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4986_: u8 = 0;
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: u8 = 0;
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut v_a_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5000_: u8 = 0;
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4970_) == 0 {
                    v___x_4977_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4977_, 0, v_b_4971_);
                    return v___x_4977_;
                } else {
                    lean_dec_ref(v_b_4971_);
                    v_head_4978_ = lean_ctor_get(v_as_x27_4970_, 0);
                    v_tail_4979_ = lean_ctor_get(v_as_x27_4970_, 1);
                    v_lhs_4980_ = lean_ctor_get(v_head_4978_, 0);
                    v_rhs_4981_ = lean_ctor_get(v_head_4978_, 1);
                    lean_inc(v___y_4975_);
                    lean_inc_ref(v___y_4974_);
                    lean_inc(v___y_4973_);
                    lean_inc_ref(v___y_4972_);
                    lean_inc_ref(v_rhs_4981_);
                    lean_inc_ref(v_lhs_4980_);
                    v___x_4982_ = lean_is_expr_def_eq(
                        v_lhs_4980_,
                        v_rhs_4981_,
                        v___y_4972_,
                        v___y_4973_,
                        v___y_4974_,
                        v___y_4975_,
                    );
                    if lean_obj_tag(v___x_4982_) == 0 {
                        v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
                        v_isSharedCheck_4996_ = (!lean_is_exclusive(v___x_4982_)) as u8;
                        if v_isSharedCheck_4996_ == 0 {
                            v___x_4985_ = v___x_4982_;
                            v_isShared_4986_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4983_);
                            lean_dec(v___x_4982_);
                            v___x_4985_ = lean_box(0);
                            v_isShared_4986_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4997_ = lean_ctor_get(v___x_4982_, 0);
                        v_isSharedCheck_5004_ = (!lean_is_exclusive(v___x_4982_)) as u8;
                        if v_isSharedCheck_5004_ == 0 {
                            v___x_4999_ = v___x_4982_;
                            v_isShared_5000_ = v_isSharedCheck_5004_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4997_);
                            lean_dec(v___x_4982_);
                            v___x_4999_ = lean_box(0);
                            v_isShared_5000_ = v_isSharedCheck_5004_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4987_ = lean_box(0);
                v___x_4988_ = (lean_unbox(v_a_4983_) as u8);
                if v___x_4988_ == 0 {
                    v___x_4989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4989_, 0, v_a_4983_);
                    v___x_4990_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4990_, 0, v___x_4989_);
                    lean_ctor_set(v___x_4990_, 1, v___x_4987_);
                    if v_isShared_4986_ == 0 {
                        lean_ctor_set(v___x_4985_, 0, v___x_4990_);
                        v___x_4992_ = v___x_4985_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4993_, 0, v___x_4990_);
                        v___x_4992_ = v_reuseFailAlloc_4993_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4985_);
                    lean_dec(v_a_4983_);
                    v___x_4994_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0;
                    v_as_x27_4970_ = v_tail_4979_;
                    v_b_4971_ = v___x_4994_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_4992_;
            }
            3 => {
                if v_isShared_5000_ == 0 {
                    v___x_5002_ = v___x_4999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
                    v___x_5002_ = v_reuseFailAlloc_5003_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___boxed(
    mut v_as_x27_5005_: *mut LeanObject,
    mut v_b_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5012_: *mut LeanObject = core::ptr::null_mut();
    v_res_5012_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_5005_, v_b_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
    lean_dec(v___y_5010_);
    lean_dec_ref(v___y_5009_);
    lean_dec(v___y_5008_);
    lean_dec_ref(v___y_5007_);
    lean_dec(v_as_x27_5005_);
    return v_res_5012_;
}
pub unsafe fn _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    v___x_5013_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5013_;
}
pub unsafe fn _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    v___x_5014_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0_once), _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__0);
    v___x_5015_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5015_, 0, v___x_5014_);
    return v___x_5015_;
}
pub unsafe fn _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8()
-> *mut LeanObject {
    let mut v_cls_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    v_cls_5028_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5;
    v___x_5029_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__7;
    v___x_5030_ = l_Lean_Name_append(v___x_5029_, v_cls_5028_);
    return v___x_5030_;
}
pub unsafe fn _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10()
-> *mut LeanObject {
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    v___x_5032_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__9;
    v___x_5033_ = l_Lean_stringToMessageData(v___x_5032_);
    return v___x_5033_;
}
pub unsafe fn l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(
    mut v_candidate_5034_: *mut LeanObject,
    mut v_t_5035_: *mut LeanObject,
    mut v_s_5036_: *mut LeanObject,
    mut v_mayPostpone_5037_: u8,
    mut v_a_5038_: *mut LeanObject,
    mut v_a_5039_: *mut LeanObject,
    mut v_a_5040_: *mut LeanObject,
    mut v_a_5041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5047_: u8 = 0;
    let mut v___y_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5050_: u8 = 0;
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut v_unused_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5067_: u8 = 0;
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: u8 = 0;
    let mut v___x_5074_: u8 = 0;
    let mut v_a_5076_: u8 = 0;
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5080_: u8 = 0;
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5085_: u8 = 0;
    let mut v_unused_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5096_: u8 = 0;
    let mut v_inferType_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funInfo_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_whnf_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqPerm_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5104_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5114_: u8 = 0;
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5121_: u8 = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut v_unused_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v_unused_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5153_: u8 = 0;
    let mut v_a_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: u8 = 0;
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5172_: u8 = 0;
    let mut v_ctxApprox_5173_: u8 = 0;
    let mut v_quasiPatternApprox_5174_: u8 = 0;
    let mut v_constApprox_5175_: u8 = 0;
    let mut v_isDefEqStuckEx_5176_: u8 = 0;
    let mut v_proofIrrelevance_5177_: u8 = 0;
    let mut v_assignSyntheticOpaque_5178_: u8 = 0;
    let mut v_offsetCnstrs_5179_: u8 = 0;
    let mut v_transparency_5180_: u8 = 0;
    let mut v_etaStruct_5181_: u8 = 0;
    let mut v_univApprox_5182_: u8 = 0;
    let mut v_iota_5183_: u8 = 0;
    let mut v_beta_5184_: u8 = 0;
    let mut v_proj_5185_: u8 = 0;
    let mut v_zeta_5186_: u8 = 0;
    let mut v_zetaDelta_5187_: u8 = 0;
    let mut v_zetaUnused_5188_: u8 = 0;
    let mut v_zetaHave_5189_: u8 = 0;
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5192_: u8 = 0;
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5195_: u8 = 0;
    let mut v_zetaDeltaSet_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5202_: u8 = 0;
    let mut v_inTypeClassResolution_5203_: u8 = 0;
    let mut v_cacheInferType_5204_: u8 = 0;
    let mut v_pattern_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constraints_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5208_: u8 = 0;
    let mut v___y_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5225_: usize = 0;
    let mut v___x_5226_: usize = 0;
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: u8 = 0;
    let mut v_a_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: u8 = 0;
    let mut v_isSharedCheck_5236_: u8 = 0;
    let mut v_unused_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5243_: u8 = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: u64 = 0;
    let mut v_cls_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: u8 = 0;
    let mut v_options_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5253_: u8 = 0;
    let mut v___x_5254_: u8 = 0;
    let mut v_inheritedTraceOptions_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: u8 = 0;
    let mut v___x_5258_: u8 = 0;
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: u8 = 0;
    let mut v_a_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: u8 = 0;
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut v_isSharedCheck_5276_: u8 = 0;
    let mut v_a_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5284_: u8 = 0;
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v_reuseFailAlloc_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5291_: u8 = 0;
    let mut v_unused_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5293_: u8 = 0;
    let mut v_isSharedCheck_5294_: u8 = 0;
    let mut v_a_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5043_ = l_Lean_Meta_saveState___redArg(v_a_5039_, v_a_5041_);
                if lean_obj_tag(v___x_5043_) == 0 {
                    v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
                    v_isSharedCheck_5294_ = (!lean_is_exclusive(v___x_5043_)) as u8;
                    if v_isSharedCheck_5294_ == 0 {
                        v___x_5046_ = v___x_5043_;
                        v_isShared_5047_ = v_isSharedCheck_5294_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5044_);
                        lean_dec(v___x_5043_);
                        v___x_5046_ = lean_box(0);
                        v_isShared_5047_ = v_isSharedCheck_5294_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_s_5036_);
                    lean_dec_ref(v_t_5035_);
                    lean_dec(v_candidate_5034_);
                    v_a_5295_ = lean_ctor_get(v___x_5043_, 0);
                    v_isSharedCheck_5302_ = (!lean_is_exclusive(v___x_5043_)) as u8;
                    if v_isSharedCheck_5302_ == 0 {
                        v___x_5297_ = v___x_5043_;
                        v_isShared_5298_ = v_isSharedCheck_5302_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_5295_);
                        lean_dec(v___x_5043_);
                        v___x_5297_ = lean_box(0);
                        v_isShared_5298_ = v_isSharedCheck_5302_;
                        state = 33;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5088_ = lean_st_ref_take(v_a_5039_);
                v_cache_5089_ = lean_ctor_get(v___x_5088_, 1);
                v_mctx_5090_ = lean_ctor_get(v___x_5088_, 0);
                v_zetaDeltaFVarIds_5091_ = lean_ctor_get(v___x_5088_, 2);
                v_postponed_5092_ = lean_ctor_get(v___x_5088_, 3);
                v_diag_5093_ = lean_ctor_get(v___x_5088_, 4);
                v_isSharedCheck_5293_ = (!lean_is_exclusive(v___x_5088_)) as u8;
                if v_isSharedCheck_5293_ == 0 {
                    v___x_5095_ = v___x_5088_;
                    v_isShared_5096_ = v_isSharedCheck_5293_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_diag_5093_);
                    lean_inc(v_postponed_5092_);
                    lean_inc(v_zetaDeltaFVarIds_5091_);
                    lean_inc(v_cache_5089_);
                    lean_inc(v_mctx_5090_);
                    lean_dec(v___x_5088_);
                    v___x_5095_ = lean_box(0);
                    v_isShared_5096_ = v_isSharedCheck_5293_;
                    state = 12;
                    continue;
                }
            }
            2 => {
                if v___y_5050_ == 0 {
                    lean_del_object(v___x_5046_);
                    v___x_5051_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_5044_, v_a_5039_, v_a_5041_);
                    lean_dec(v_a_5044_);
                    if lean_obj_tag(v___x_5051_) == 0 {
                        v_isSharedCheck_5058_ = (!lean_is_exclusive(v___x_5051_)) as u8;
                        if v_isSharedCheck_5058_ == 0 {
                            v_unused_5059_ = lean_ctor_get(v___x_5051_, 0);
                            lean_dec(v_unused_5059_);
                            v___x_5053_ = v___x_5051_;
                            v_isShared_5054_ = v_isSharedCheck_5058_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_5051_);
                            v___x_5053_ = lean_box(0);
                            v_isShared_5054_ = v_isSharedCheck_5058_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___y_5049_);
                        v_a_5060_ = lean_ctor_get(v___x_5051_, 0);
                        v_isSharedCheck_5067_ = (!lean_is_exclusive(v___x_5051_)) as u8;
                        if v_isSharedCheck_5067_ == 0 {
                            v___x_5062_ = v___x_5051_;
                            v_isShared_5063_ = v_isSharedCheck_5067_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5060_);
                            lean_dec(v___x_5051_);
                            v___x_5062_ = lean_box(0);
                            v_isShared_5063_ = v_isSharedCheck_5067_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5044_);
                    if v_isShared_5047_ == 0 {
                        lean_ctor_set_tag(v___x_5046_, 1);
                        lean_ctor_set(v___x_5046_, 0, v___y_5049_);
                        v___x_5069_ = v___x_5046_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___y_5049_);
                        v___x_5069_ = v_reuseFailAlloc_5070_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5054_ == 0 {
                    lean_ctor_set_tag(v___x_5053_, 1);
                    lean_ctor_set(v___x_5053_, 0, v___y_5049_);
                    v___x_5056_ = v___x_5053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___y_5049_);
                    v___x_5056_ = v_reuseFailAlloc_5057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5056_;
            }
            5 => {
                if v_isShared_5063_ == 0 {
                    v___x_5065_ = v___x_5062_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
                    v___x_5065_ = v_reuseFailAlloc_5066_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5065_;
            }
            7 => {
                return v___x_5069_;
            }
            8 => {
                v___x_5073_ = l_Lean_Exception_isInterrupt(v_a_5072_);
                if v___x_5073_ == 0 {
                    lean_inc_ref(v_a_5072_);
                    v___x_5074_ = l_Lean_Exception_isRuntime(v_a_5072_);
                    v___y_5049_ = v_a_5072_;
                    v___y_5050_ = v___x_5074_;
                    state = 2;
                    continue;
                } else {
                    v___y_5049_ = v_a_5072_;
                    v___y_5050_ = v___x_5073_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v___x_5077_ =
                    l_Lean_Meta_SavedState_restore___redArg(v_a_5044_, v_a_5039_, v_a_5041_);
                if lean_obj_tag(v___x_5077_) == 0 {
                    lean_del_object(v___x_5046_);
                    lean_dec(v_a_5044_);
                    v_isSharedCheck_5085_ = (!lean_is_exclusive(v___x_5077_)) as u8;
                    if v_isSharedCheck_5085_ == 0 {
                        v_unused_5086_ = lean_ctor_get(v___x_5077_, 0);
                        lean_dec(v_unused_5086_);
                        v___x_5079_ = v___x_5077_;
                        v_isShared_5080_ = v_isSharedCheck_5085_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec(v___x_5077_);
                        v___x_5079_ = lean_box(0);
                        v_isShared_5080_ = v_isSharedCheck_5085_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_5087_ = lean_ctor_get(v___x_5077_, 0);
                    lean_inc(v_a_5087_);
                    lean_dec_ref_known(v___x_5077_, 1);
                    v_a_5072_ = v_a_5087_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_5081_ = lean_box((v_a_5076_) as usize);
                if v_isShared_5080_ == 0 {
                    lean_ctor_set(v___x_5079_, 0, v___x_5081_);
                    v___x_5083_ = v___x_5079_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5081_);
                    v___x_5083_ = v_reuseFailAlloc_5084_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5083_;
            }
            12 => {
                v_inferType_5097_ = lean_ctor_get(v_cache_5089_, 0);
                v_funInfo_5098_ = lean_ctor_get(v_cache_5089_, 1);
                v_synthInstance_5099_ = lean_ctor_get(v_cache_5089_, 2);
                v_whnf_5100_ = lean_ctor_get(v_cache_5089_, 3);
                v_defEqPerm_5101_ = lean_ctor_get(v_cache_5089_, 5);
                v_isSharedCheck_5291_ = (!lean_is_exclusive(v_cache_5089_)) as u8;
                if v_isSharedCheck_5291_ == 0 {
                    v_unused_5292_ = lean_ctor_get(v_cache_5089_, 4);
                    lean_dec(v_unused_5292_);
                    v___x_5103_ = v_cache_5089_;
                    v_isShared_5104_ = v_isSharedCheck_5291_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_defEqPerm_5101_);
                    lean_inc(v_whnf_5100_);
                    lean_inc(v_synthInstance_5099_);
                    lean_inc(v_funInfo_5098_);
                    lean_inc(v_inferType_5097_);
                    lean_dec(v_cache_5089_);
                    v___x_5103_ = lean_box(0);
                    v_isShared_5104_ = v_isSharedCheck_5291_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5105_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1_once), _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__1);
                if v_isShared_5104_ == 0 {
                    lean_ctor_set(v___x_5103_, 4, v___x_5105_);
                    v___x_5107_ = v___x_5103_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_inferType_5097_);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 1, v_funInfo_5098_);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 2, v_synthInstance_5099_);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 3, v_whnf_5100_);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 4, v___x_5105_);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 5, v_defEqPerm_5101_);
                    v___x_5107_ = v_reuseFailAlloc_5290_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5096_ == 0 {
                    lean_ctor_set(v___x_5095_, 1, v___x_5107_);
                    v___x_5109_ = v___x_5095_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5289_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_mctx_5090_);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 1, v___x_5107_);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 2, v_zetaDeltaFVarIds_5091_);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 3, v_postponed_5092_);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 4, v_diag_5093_);
                    v___x_5109_ = v_reuseFailAlloc_5289_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_5110_ = lean_st_ref_set(v_a_5039_, v___x_5109_);
                v___x_5111_ = l_Lean_Meta_getResetPostponed___redArg(v_a_5039_);
                if lean_obj_tag(v___x_5111_) == 0 {
                    v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
                    lean_inc(v_a_5112_);
                    lean_dec_ref_known(v___x_5111_, 1);
                    lean_inc(v_candidate_5034_);
                    v___x_5155_ = l_Lean_getConstInfo___at___00Lean_Meta_addUnificationHint_spec__0(
                        v_candidate_5034_,
                        v_a_5038_,
                        v_a_5039_,
                        v_a_5040_,
                        v_a_5041_,
                    );
                    if lean_obj_tag(v___x_5155_) == 0 {
                        v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
                        lean_inc(v_a_5156_);
                        lean_dec_ref_known(v___x_5155_, 1);
                        v___x_5157_ = l_Lean_ConstantInfo_levelParams(v_a_5156_);
                        v___x_5158_ = lean_box(0);
                        v___x_5159_ = l_List_mapM_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__0(v___x_5157_, v___x_5158_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
                        if lean_obj_tag(v___x_5159_) == 0 {
                            v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
                            lean_inc(v_a_5160_);
                            lean_dec_ref_known(v___x_5159_, 1);
                            v___x_5161_ = 0;
                            v___x_5162_ = l_Lean_Core_instantiateValueLevelParams(
                                v_a_5156_,
                                v_a_5160_,
                                v___x_5161_,
                                v_a_5040_,
                                v_a_5041_,
                            );
                            lean_dec(v_a_5156_);
                            if lean_obj_tag(v___x_5162_) == 0 {
                                v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
                                lean_inc(v_a_5163_);
                                lean_dec_ref_known(v___x_5162_, 1);
                                v___x_5164_ = lean_box(0);
                                v___x_5165_ = l_Lean_Meta_lambdaMetaTelescope(
                                    v_a_5163_,
                                    v___x_5164_,
                                    v_a_5038_,
                                    v_a_5039_,
                                    v_a_5040_,
                                    v_a_5041_,
                                );
                                lean_dec(v_a_5163_);
                                if lean_obj_tag(v___x_5165_) == 0 {
                                    v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
                                    lean_inc(v_a_5166_);
                                    lean_dec_ref_known(v___x_5165_, 1);
                                    v_snd_5167_ = lean_ctor_get(v_a_5166_, 1);
                                    lean_inc(v_snd_5167_);
                                    v_fst_5168_ = lean_ctor_get(v_a_5166_, 0);
                                    lean_inc(v_fst_5168_);
                                    lean_dec(v_a_5166_);
                                    v_fst_5169_ = lean_ctor_get(v_snd_5167_, 0);
                                    lean_inc(v_fst_5169_);
                                    v_snd_5170_ = lean_ctor_get(v_snd_5167_, 1);
                                    lean_inc(v_snd_5170_);
                                    lean_dec(v_snd_5167_);
                                    v___x_5171_ = l_Lean_Meta_Context_config(v_a_5038_);
                                    v_foApprox_5172_ = lean_ctor_get_uint8(v___x_5171_, 0 as u32);
                                    v_ctxApprox_5173_ = lean_ctor_get_uint8(v___x_5171_, 1 as u32);
                                    v_quasiPatternApprox_5174_ =
                                        lean_ctor_get_uint8(v___x_5171_, 2 as u32);
                                    v_constApprox_5175_ =
                                        lean_ctor_get_uint8(v___x_5171_, 3 as u32);
                                    v_isDefEqStuckEx_5176_ =
                                        lean_ctor_get_uint8(v___x_5171_, 4 as u32);
                                    v_proofIrrelevance_5177_ =
                                        lean_ctor_get_uint8(v___x_5171_, 6 as u32);
                                    v_assignSyntheticOpaque_5178_ =
                                        lean_ctor_get_uint8(v___x_5171_, 7 as u32);
                                    v_offsetCnstrs_5179_ =
                                        lean_ctor_get_uint8(v___x_5171_, 8 as u32);
                                    v_transparency_5180_ =
                                        lean_ctor_get_uint8(v___x_5171_, 9 as u32);
                                    v_etaStruct_5181_ = lean_ctor_get_uint8(v___x_5171_, 10 as u32);
                                    v_univApprox_5182_ =
                                        lean_ctor_get_uint8(v___x_5171_, 11 as u32);
                                    v_iota_5183_ = lean_ctor_get_uint8(v___x_5171_, 12 as u32);
                                    v_beta_5184_ = lean_ctor_get_uint8(v___x_5171_, 13 as u32);
                                    v_proj_5185_ = lean_ctor_get_uint8(v___x_5171_, 14 as u32);
                                    v_zeta_5186_ = lean_ctor_get_uint8(v___x_5171_, 15 as u32);
                                    v_zetaDelta_5187_ = lean_ctor_get_uint8(v___x_5171_, 16 as u32);
                                    v_zetaUnused_5188_ =
                                        lean_ctor_get_uint8(v___x_5171_, 17 as u32);
                                    v_zetaHave_5189_ = lean_ctor_get_uint8(v___x_5171_, 18 as u32);
                                    v_isSharedCheck_5276_ = (!lean_is_exclusive(v___x_5171_)) as u8;
                                    if v_isSharedCheck_5276_ == 0 {
                                        v___x_5191_ = v___x_5171_;
                                        v_isShared_5192_ = v_isSharedCheck_5276_;
                                        state = 23;
                                        continue;
                                    } else {
                                        lean_dec(v___x_5171_);
                                        v___x_5191_ = lean_box(0);
                                        v_isShared_5192_ = v_isSharedCheck_5276_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_5112_);
                                    lean_dec_ref(v_s_5036_);
                                    lean_dec_ref(v_t_5035_);
                                    lean_dec(v_candidate_5034_);
                                    v_a_5277_ = lean_ctor_get(v___x_5165_, 0);
                                    lean_inc(v_a_5277_);
                                    lean_dec_ref_known(v___x_5165_, 1);
                                    v_a_5072_ = v_a_5277_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5112_);
                                lean_dec_ref(v_s_5036_);
                                lean_dec_ref(v_t_5035_);
                                lean_dec(v_candidate_5034_);
                                v_a_5278_ = lean_ctor_get(v___x_5162_, 0);
                                lean_inc(v_a_5278_);
                                lean_dec_ref_known(v___x_5162_, 1);
                                v_a_5072_ = v_a_5278_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5156_);
                            lean_dec(v_a_5112_);
                            lean_dec_ref(v_s_5036_);
                            lean_dec_ref(v_t_5035_);
                            lean_dec(v_candidate_5034_);
                            v_a_5279_ = lean_ctor_get(v___x_5159_, 0);
                            lean_inc(v_a_5279_);
                            lean_dec_ref_known(v___x_5159_, 1);
                            v_a_5072_ = v_a_5279_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5112_);
                        lean_dec_ref(v_s_5036_);
                        lean_dec_ref(v_t_5035_);
                        lean_dec(v_candidate_5034_);
                        v_a_5280_ = lean_ctor_get(v___x_5155_, 0);
                        lean_inc(v_a_5280_);
                        lean_dec_ref_known(v___x_5155_, 1);
                        v_a_5072_ = v_a_5280_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5046_);
                    lean_dec(v_a_5044_);
                    lean_dec_ref(v_s_5036_);
                    lean_dec_ref(v_t_5035_);
                    lean_dec(v_candidate_5034_);
                    v_a_5281_ = lean_ctor_get(v___x_5111_, 0);
                    v_isSharedCheck_5288_ = (!lean_is_exclusive(v___x_5111_)) as u8;
                    if v_isSharedCheck_5288_ == 0 {
                        v___x_5283_ = v___x_5111_;
                        v_isShared_5284_ = v_isSharedCheck_5288_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_5281_);
                        lean_dec(v___x_5111_);
                        v___x_5283_ = lean_box(0);
                        v_isShared_5284_ = v_isSharedCheck_5288_;
                        state = 31;
                        continue;
                    }
                }
            }
            16 => {
                if v_a_5114_ == 0 {
                    lean_dec(v_a_5112_);
                    v_a_5076_ = v_a_5114_;
                    state = 9;
                    continue;
                } else {
                    v___x_5115_ = 0;
                    v___x_5116_ = l_Lean_Meta_processPostponed(
                        v_mayPostpone_5037_,
                        v___x_5115_,
                        v_a_5038_,
                        v_a_5039_,
                        v_a_5040_,
                        v_a_5041_,
                    );
                    if lean_obj_tag(v___x_5116_) == 0 {
                        v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
                        v_isSharedCheck_5153_ = (!lean_is_exclusive(v___x_5116_)) as u8;
                        if v_isSharedCheck_5153_ == 0 {
                            v___x_5119_ = v___x_5116_;
                            v_isShared_5120_ = v_isSharedCheck_5153_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_5117_);
                            lean_dec(v___x_5116_);
                            v___x_5119_ = lean_box(0);
                            v_isShared_5120_ = v_isSharedCheck_5153_;
                            state = 17;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5112_);
                        v_a_5154_ = lean_ctor_get(v___x_5116_, 0);
                        lean_inc(v_a_5154_);
                        lean_dec_ref_known(v___x_5116_, 1);
                        v_a_5072_ = v_a_5154_;
                        state = 8;
                        continue;
                    }
                }
            }
            17 => {
                v___x_5121_ = (lean_unbox(v_a_5117_) as u8);
                if v___x_5121_ == 0 {
                    lean_del_object(v___x_5119_);
                    lean_dec(v_a_5117_);
                    lean_dec(v_a_5112_);
                    v___x_5122_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_5044_, v_a_5039_, v_a_5041_);
                    if lean_obj_tag(v___x_5122_) == 0 {
                        lean_del_object(v___x_5046_);
                        lean_dec(v_a_5044_);
                        v_isSharedCheck_5130_ = (!lean_is_exclusive(v___x_5122_)) as u8;
                        if v_isSharedCheck_5130_ == 0 {
                            v_unused_5131_ = lean_ctor_get(v___x_5122_, 0);
                            lean_dec(v_unused_5131_);
                            v___x_5124_ = v___x_5122_;
                            v_isShared_5125_ = v_isSharedCheck_5130_;
                            state = 18;
                            continue;
                        } else {
                            lean_dec(v___x_5122_);
                            v___x_5124_ = lean_box(0);
                            v_isShared_5125_ = v_isSharedCheck_5130_;
                            state = 18;
                            continue;
                        }
                    } else {
                        v_a_5132_ = lean_ctor_get(v___x_5122_, 0);
                        lean_inc(v_a_5132_);
                        lean_dec_ref_known(v___x_5122_, 1);
                        v_a_5072_ = v_a_5132_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5046_);
                    lean_dec(v_a_5044_);
                    v___x_5133_ = lean_st_ref_get(v_a_5039_);
                    v___x_5134_ = lean_st_ref_take(v_a_5039_);
                    v_postponed_5135_ = lean_ctor_get(v___x_5133_, 3);
                    lean_inc_ref(v_postponed_5135_);
                    lean_dec(v___x_5133_);
                    v_mctx_5136_ = lean_ctor_get(v___x_5134_, 0);
                    v_cache_5137_ = lean_ctor_get(v___x_5134_, 1);
                    v_zetaDeltaFVarIds_5138_ = lean_ctor_get(v___x_5134_, 2);
                    v_diag_5139_ = lean_ctor_get(v___x_5134_, 4);
                    v_isSharedCheck_5151_ = (!lean_is_exclusive(v___x_5134_)) as u8;
                    if v_isSharedCheck_5151_ == 0 {
                        v_unused_5152_ = lean_ctor_get(v___x_5134_, 3);
                        lean_dec(v_unused_5152_);
                        v___x_5141_ = v___x_5134_;
                        v_isShared_5142_ = v_isSharedCheck_5151_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_diag_5139_);
                        lean_inc(v_zetaDeltaFVarIds_5138_);
                        lean_inc(v_cache_5137_);
                        lean_inc(v_mctx_5136_);
                        lean_dec(v___x_5134_);
                        v___x_5141_ = lean_box(0);
                        v_isShared_5142_ = v_isSharedCheck_5151_;
                        state = 20;
                        continue;
                    }
                }
            }
            18 => {
                v___x_5126_ = lean_box((v___x_5115_) as usize);
                if v_isShared_5125_ == 0 {
                    lean_ctor_set(v___x_5124_, 0, v___x_5126_);
                    v___x_5128_ = v___x_5124_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
                    v___x_5128_ = v_reuseFailAlloc_5129_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5128_;
            }
            20 => {
                v___x_5143_ = l_Lean_PersistentArray_append___redArg(v_a_5112_, v_postponed_5135_);
                lean_dec_ref(v_postponed_5135_);
                if v_isShared_5142_ == 0 {
                    lean_ctor_set(v___x_5141_, 3, v___x_5143_);
                    v___x_5145_ = v___x_5141_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_mctx_5136_);
                    lean_ctor_set(v_reuseFailAlloc_5150_, 1, v_cache_5137_);
                    lean_ctor_set(v_reuseFailAlloc_5150_, 2, v_zetaDeltaFVarIds_5138_);
                    lean_ctor_set(v_reuseFailAlloc_5150_, 3, v___x_5143_);
                    lean_ctor_set(v_reuseFailAlloc_5150_, 4, v_diag_5139_);
                    v___x_5145_ = v_reuseFailAlloc_5150_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_5146_ = lean_st_ref_set(v_a_5039_, v___x_5145_);
                if v_isShared_5120_ == 0 {
                    v___x_5148_ = v___x_5119_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5117_);
                    v___x_5148_ = v_reuseFailAlloc_5149_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5148_;
            }
            23 => {
                v___x_5193_ =
                    l___private_Lean_Meta_UnificationHint_0__Lean_Meta_decodeUnificationHint(
                        v_snd_5170_,
                    );
                if lean_obj_tag(v___x_5193_) == 0 {
                    lean_dec_ref_known(v___x_5193_, 1);
                    lean_del_object(v___x_5191_);
                    lean_dec(v_fst_5169_);
                    lean_dec(v_fst_5168_);
                    lean_dec(v_a_5112_);
                    lean_dec_ref(v_s_5036_);
                    lean_dec_ref(v_t_5035_);
                    lean_dec(v_candidate_5034_);
                    v_a_5076_ = v___x_5161_;
                    state = 9;
                    continue;
                } else {
                    v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
                    lean_inc(v_a_5194_);
                    lean_dec_ref_known(v___x_5193_, 1);
                    v_trackZetaDelta_5195_ = lean_ctor_get_uint8(
                        v_a_5038_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    );
                    v_zetaDeltaSet_5196_ = lean_ctor_get(v_a_5038_, 1);
                    v_lctx_5197_ = lean_ctor_get(v_a_5038_, 2);
                    v_localInstances_5198_ = lean_ctor_get(v_a_5038_, 3);
                    v_defEqCtx_x3f_5199_ = lean_ctor_get(v_a_5038_, 4);
                    v_synthPendingDepth_5200_ = lean_ctor_get(v_a_5038_, 5);
                    v_canUnfold_x3f_5201_ = lean_ctor_get(v_a_5038_, 6);
                    v_univApprox_5202_ = lean_ctor_get_uint8(
                        v_a_5038_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    );
                    v_inTypeClassResolution_5203_ = lean_ctor_get_uint8(
                        v_a_5038_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    );
                    v_cacheInferType_5204_ = lean_ctor_get_uint8(
                        v_a_5038_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    );
                    v_pattern_5205_ = lean_ctor_get(v_a_5194_, 0);
                    lean_inc_ref(v_pattern_5205_);
                    v_constraints_5206_ = lean_ctor_get(v_a_5194_, 1);
                    lean_inc(v_constraints_5206_);
                    lean_dec(v_a_5194_);
                    v_lhs_5239_ = lean_ctor_get(v_pattern_5205_, 0);
                    v_rhs_5240_ = lean_ctor_get(v_pattern_5205_, 1);
                    v_isSharedCheck_5275_ = (!lean_is_exclusive(v_pattern_5205_)) as u8;
                    if v_isSharedCheck_5275_ == 0 {
                        v___x_5242_ = v_pattern_5205_;
                        v_isShared_5243_ = v_isSharedCheck_5275_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_rhs_5240_);
                        lean_inc(v_lhs_5239_);
                        lean_dec(v_pattern_5205_);
                        v___x_5242_ = lean_box(0);
                        v_isShared_5243_ = v_isSharedCheck_5275_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                v___x_5213_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__2;
                v___x_5214_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_constraints_5206_, v___x_5213_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
                lean_dec(v_constraints_5206_);
                if lean_obj_tag(v___x_5214_) == 0 {
                    v_a_5215_ = lean_ctor_get(v___x_5214_, 0);
                    lean_inc(v_a_5215_);
                    lean_dec_ref_known(v___x_5214_, 1);
                    v_fst_5216_ = lean_ctor_get(v_a_5215_, 0);
                    v_isSharedCheck_5236_ = (!lean_is_exclusive(v_a_5215_)) as u8;
                    if v_isSharedCheck_5236_ == 0 {
                        v_unused_5237_ = lean_ctor_get(v_a_5215_, 1);
                        lean_dec(v_unused_5237_);
                        v___x_5218_ = v_a_5215_;
                        v_isShared_5219_ = v_isSharedCheck_5236_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_fst_5216_);
                        lean_dec(v_a_5215_);
                        v___x_5218_ = lean_box(0);
                        v_isShared_5219_ = v_isSharedCheck_5236_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_5169_);
                    lean_dec(v_fst_5168_);
                    lean_dec(v_a_5112_);
                    v_a_5238_ = lean_ctor_get(v___x_5214_, 0);
                    lean_inc(v_a_5238_);
                    lean_dec_ref_known(v___x_5214_, 1);
                    v_a_5072_ = v_a_5238_;
                    state = 8;
                    continue;
                }
            }
            25 => {
                if lean_obj_tag(v_fst_5216_) == 0 {
                    v___x_5220_ = lean_unsigned_to_nat(0);
                    v___x_5221_ = lean_array_get_size(v_fst_5169_);
                    v___x_5222_ =
                        l_Array_toSubarray___redArg(v_fst_5169_, v___x_5220_, v___x_5221_);
                    if v_isShared_5219_ == 0 {
                        lean_ctor_set(v___x_5218_, 1, v___x_5222_);
                        lean_ctor_set(v___x_5218_, 0, v___x_5164_);
                        v___x_5224_ = v___x_5218_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5164_);
                        lean_ctor_set(v_reuseFailAlloc_5233_, 1, v___x_5222_);
                        v___x_5224_ = v_reuseFailAlloc_5233_;
                        state = 26;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5218_);
                    lean_dec(v_fst_5169_);
                    lean_dec(v_fst_5168_);
                    v_val_5234_ = lean_ctor_get(v_fst_5216_, 0);
                    lean_inc(v_val_5234_);
                    lean_dec_ref_known(v_fst_5216_, 1);
                    v___x_5235_ = (lean_unbox(v_val_5234_) as u8);
                    lean_dec(v_val_5234_);
                    v_a_5114_ = v___x_5235_;
                    state = 16;
                    continue;
                }
            }
            26 => {
                v_sz_5225_ = lean_array_size(v_fst_5168_);
                v___x_5226_ = 0usize;
                v___x_5227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__2(v_fst_5168_, v_sz_5225_, v___x_5226_, v___x_5224_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
                lean_dec(v_fst_5168_);
                if lean_obj_tag(v___x_5227_) == 0 {
                    v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
                    lean_inc(v_a_5228_);
                    lean_dec_ref_known(v___x_5227_, 1);
                    v_fst_5229_ = lean_ctor_get(v_a_5228_, 0);
                    lean_inc(v_fst_5229_);
                    lean_dec(v_a_5228_);
                    if lean_obj_tag(v_fst_5229_) == 0 {
                        v_a_5114_ = v___y_5208_;
                        state = 16;
                        continue;
                    } else {
                        v_val_5230_ = lean_ctor_get(v_fst_5229_, 0);
                        lean_inc(v_val_5230_);
                        lean_dec_ref_known(v_fst_5229_, 1);
                        v___x_5231_ = (lean_unbox(v_val_5230_) as u8);
                        lean_dec(v_val_5230_);
                        v_a_5114_ = v___x_5231_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5112_);
                    v_a_5232_ = lean_ctor_get(v___x_5227_, 0);
                    lean_inc(v_a_5232_);
                    lean_dec_ref_known(v___x_5227_, 1);
                    v_a_5072_ = v_a_5232_;
                    state = 8;
                    continue;
                }
            }
            27 => {
                if v_isShared_5192_ == 0 {
                    v___x_5245_ = v___x_5191_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 0 as u32, v_foApprox_5172_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 1 as u32, v_ctxApprox_5173_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5274_,
                        2 as u32,
                        v_quasiPatternApprox_5174_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 3 as u32, v_constApprox_5175_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 4 as u32, v_isDefEqStuckEx_5176_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 6 as u32, v_proofIrrelevance_5177_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5274_,
                        7 as u32,
                        v_assignSyntheticOpaque_5178_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 8 as u32, v_offsetCnstrs_5179_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 9 as u32, v_transparency_5180_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 10 as u32, v_etaStruct_5181_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 11 as u32, v_univApprox_5182_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 12 as u32, v_iota_5183_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 13 as u32, v_beta_5184_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 14 as u32, v_proj_5185_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 15 as u32, v_zeta_5186_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 16 as u32, v_zetaDelta_5187_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 17 as u32, v_zetaUnused_5188_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5274_, 18 as u32, v_zetaHave_5189_);
                    v___x_5245_ = v_reuseFailAlloc_5274_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                lean_ctor_set_uint8(v___x_5245_, 5 as u32, v___x_5161_);
                v___x_5246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5245_);
                v_cls_5247_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5;
                v___x_5268_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5268_, 0, v___x_5245_);
                lean_ctor_set_uint64(
                    v___x_5268_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5246_,
                );
                lean_inc(v_canUnfold_x3f_5201_);
                lean_inc(v_synthPendingDepth_5200_);
                lean_inc(v_defEqCtx_x3f_5199_);
                lean_inc_ref(v_localInstances_5198_);
                lean_inc_ref(v_lctx_5197_);
                lean_inc(v_zetaDeltaSet_5196_);
                v___x_5269_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5269_, 0, v___x_5268_);
                lean_ctor_set(v___x_5269_, 1, v_zetaDeltaSet_5196_);
                lean_ctor_set(v___x_5269_, 2, v_lctx_5197_);
                lean_ctor_set(v___x_5269_, 3, v_localInstances_5198_);
                lean_ctor_set(v___x_5269_, 4, v_defEqCtx_x3f_5199_);
                lean_ctor_set(v___x_5269_, 5, v_synthPendingDepth_5200_);
                lean_ctor_set(v___x_5269_, 6, v_canUnfold_x3f_5201_);
                lean_ctor_set_uint8(
                    v___x_5269_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5195_,
                );
                lean_ctor_set_uint8(
                    v___x_5269_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5202_,
                );
                lean_ctor_set_uint8(
                    v___x_5269_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5203_,
                );
                lean_ctor_set_uint8(
                    v___x_5269_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5204_,
                );
                v___x_5270_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_lhs_5239_, v_t_5035_, v___x_5269_, v_a_5039_, v_a_5040_, v_a_5041_);
                if lean_obj_tag(v___x_5270_) == 0 {
                    v_a_5271_ = lean_ctor_get(v___x_5270_, 0);
                    lean_inc(v_a_5271_);
                    v___x_5272_ = (lean_unbox(v_a_5271_) as u8);
                    lean_dec(v_a_5271_);
                    if v___x_5272_ == 0 {
                        lean_dec_ref_known(v___x_5269_, 7);
                        lean_dec_ref(v_rhs_5240_);
                        lean_dec_ref(v_s_5036_);
                        v___y_5249_ = v___x_5270_;
                        state = 29;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_5270_, 1);
                        v___x_5273_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_isDefEqPattern(v_rhs_5240_, v_s_5036_, v___x_5269_, v_a_5039_, v_a_5040_, v_a_5041_);
                        lean_dec_ref_known(v___x_5269_, 7);
                        v___y_5249_ = v___x_5273_;
                        state = 29;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_5269_, 7);
                    lean_dec_ref(v_rhs_5240_);
                    lean_dec_ref(v_s_5036_);
                    v___y_5249_ = v___x_5270_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if lean_obj_tag(v___y_5249_) == 0 {
                    v_a_5250_ = lean_ctor_get(v___y_5249_, 0);
                    lean_inc(v_a_5250_);
                    lean_dec_ref_known(v___y_5249_, 1);
                    v___x_5251_ = (lean_unbox(v_a_5250_) as u8);
                    if v___x_5251_ == 0 {
                        lean_dec(v_a_5250_);
                        lean_del_object(v___x_5242_);
                        lean_dec(v_constraints_5206_);
                        lean_dec(v_fst_5169_);
                        lean_dec(v_fst_5168_);
                        lean_dec(v_a_5112_);
                        lean_dec(v_candidate_5034_);
                        v_a_5076_ = v___x_5161_;
                        state = 9;
                        continue;
                    } else {
                        v_options_5252_ = lean_ctor_get(v_a_5040_, 2);
                        v_hasTrace_5253_ = lean_ctor_get_uint8(
                            v_options_5252_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_5253_ == 0 {
                            lean_del_object(v___x_5242_);
                            lean_dec(v_candidate_5034_);
                            v___x_5254_ = (lean_unbox(v_a_5250_) as u8);
                            lean_dec(v_a_5250_);
                            v___y_5208_ = v___x_5254_;
                            v___y_5209_ = v_a_5038_;
                            v___y_5210_ = v_a_5039_;
                            v___y_5211_ = v_a_5040_;
                            v___y_5212_ = v_a_5041_;
                            state = 24;
                            continue;
                        } else {
                            v_inheritedTraceOptions_5255_ = lean_ctor_get(v_a_5040_, 13);
                            v___x_5256_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once), _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
                            v___x_5257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5255_,
                                v_options_5252_,
                                v___x_5256_,
                            );
                            if v___x_5257_ == 0 {
                                lean_del_object(v___x_5242_);
                                lean_dec(v_candidate_5034_);
                                v___x_5258_ = (lean_unbox(v_a_5250_) as u8);
                                lean_dec(v_a_5250_);
                                v___y_5208_ = v___x_5258_;
                                v___y_5209_ = v_a_5038_;
                                v___y_5210_ = v_a_5039_;
                                v___y_5211_ = v_a_5040_;
                                v___y_5212_ = v_a_5041_;
                                state = 24;
                                continue;
                            } else {
                                v___x_5259_ = l_Lean_MessageData_ofName(v_candidate_5034_);
                                v___x_5260_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10), core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10_once), _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__10);
                                if v_isShared_5243_ == 0 {
                                    lean_ctor_set_tag(v___x_5242_, 7);
                                    lean_ctor_set(v___x_5242_, 1, v___x_5260_);
                                    lean_ctor_set(v___x_5242_, 0, v___x_5259_);
                                    v___x_5262_ = v___x_5242_;
                                    state = 30;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5266_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5259_);
                                    lean_ctor_set(v_reuseFailAlloc_5266_, 1, v___x_5260_);
                                    v___x_5262_ = v_reuseFailAlloc_5266_;
                                    state = 30;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5242_);
                    lean_dec(v_constraints_5206_);
                    lean_dec(v_fst_5169_);
                    lean_dec(v_fst_5168_);
                    lean_dec(v_a_5112_);
                    lean_dec(v_candidate_5034_);
                    v_a_5267_ = lean_ctor_get(v___y_5249_, 0);
                    lean_inc(v_a_5267_);
                    lean_dec_ref_known(v___y_5249_, 1);
                    v_a_5072_ = v_a_5267_;
                    state = 8;
                    continue;
                }
            }
            30 => {
                v___x_5263_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_5247_, v___x_5262_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
                if lean_obj_tag(v___x_5263_) == 0 {
                    lean_dec_ref_known(v___x_5263_, 1);
                    v___x_5264_ = (lean_unbox(v_a_5250_) as u8);
                    lean_dec(v_a_5250_);
                    v___y_5208_ = v___x_5264_;
                    v___y_5209_ = v_a_5038_;
                    v___y_5210_ = v_a_5039_;
                    v___y_5211_ = v_a_5040_;
                    v___y_5212_ = v_a_5041_;
                    state = 24;
                    continue;
                } else {
                    lean_dec(v_a_5250_);
                    lean_dec(v_constraints_5206_);
                    lean_dec(v_fst_5169_);
                    lean_dec(v_fst_5168_);
                    lean_dec(v_a_5112_);
                    v_a_5265_ = lean_ctor_get(v___x_5263_, 0);
                    lean_inc(v_a_5265_);
                    lean_dec_ref_known(v___x_5263_, 1);
                    v_a_5072_ = v_a_5265_;
                    state = 8;
                    continue;
                }
            }
            31 => {
                if v_isShared_5284_ == 0 {
                    v___x_5286_ = v___x_5283_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
                    v___x_5286_ = v_reuseFailAlloc_5287_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5286_;
            }
            33 => {
                if v_isShared_5298_ == 0 {
                    v___x_5300_ = v___x_5297_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
                    v___x_5300_ = v_reuseFailAlloc_5301_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___boxed(
    mut v_candidate_5303_: *mut LeanObject,
    mut v_t_5304_: *mut LeanObject,
    mut v_s_5305_: *mut LeanObject,
    mut v_mayPostpone_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
    mut v_a_5308_: *mut LeanObject,
    mut v_a_5309_: *mut LeanObject,
    mut v_a_5310_: *mut LeanObject,
    mut v_a_5311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mayPostpone_boxed_5312_: u8 = 0;
    let mut v_res_5313_: *mut LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_5312_ = (lean_unbox(v_mayPostpone_5306_) as u8);
    v_res_5313_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_5303_, v_t_5304_, v_s_5305_, v_mayPostpone_boxed_5312_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_);
    lean_dec(v_a_5310_);
    lean_dec_ref(v_a_5309_);
    lean_dec(v_a_5308_);
    lean_dec_ref(v_a_5307_);
    return v_res_5313_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    v___x_5314_ = lean_unsigned_to_nat(32);
    v___x_5315_ = lean_mk_empty_array_with_capacity(v___x_5314_);
    v___x_5316_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5316_, 0, v___x_5315_);
    return v___x_5316_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5317_: usize = 0;
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    v___x_5317_ = 5usize;
    v___x_5318_ = lean_unsigned_to_nat(0);
    v___x_5319_ = lean_unsigned_to_nat(32);
    v___x_5320_ = lean_mk_empty_array_with_capacity(v___x_5319_);
    v___x_5321_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__0);
    v___x_5322_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5322_, 0, v___x_5321_);
    lean_ctor_set(v___x_5322_, 1, v___x_5320_);
    lean_ctor_set(v___x_5322_, 2, v___x_5318_);
    lean_ctor_set(v___x_5322_, 3, v___x_5318_);
    lean_ctor_set_usize(v___x_5322_, 4, v___x_5317_);
    return v___x_5322_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(
    mut v___y_5323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5340_: u8 = 0;
    let mut v_tid_5341_: u64 = 0;
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut v_unused_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5325_ = lean_st_ref_get(v___y_5323_);
                v_traceState_5326_ = lean_ctor_get(v___x_5325_, 4);
                lean_inc_ref(v_traceState_5326_);
                lean_dec(v___x_5325_);
                v_traces_5327_ = lean_ctor_get(v_traceState_5326_, 0);
                lean_inc_ref(v_traces_5327_);
                lean_dec_ref(v_traceState_5326_);
                v___x_5328_ = lean_st_ref_take(v___y_5323_);
                v_traceState_5329_ = lean_ctor_get(v___x_5328_, 4);
                v_env_5330_ = lean_ctor_get(v___x_5328_, 0);
                v_nextMacroScope_5331_ = lean_ctor_get(v___x_5328_, 1);
                v_ngen_5332_ = lean_ctor_get(v___x_5328_, 2);
                v_auxDeclNGen_5333_ = lean_ctor_get(v___x_5328_, 3);
                v_cache_5334_ = lean_ctor_get(v___x_5328_, 5);
                v_messages_5335_ = lean_ctor_get(v___x_5328_, 6);
                v_infoState_5336_ = lean_ctor_get(v___x_5328_, 7);
                v_snapshotTasks_5337_ = lean_ctor_get(v___x_5328_, 8);
                v_isSharedCheck_5356_ = (!lean_is_exclusive(v___x_5328_)) as u8;
                if v_isSharedCheck_5356_ == 0 {
                    v___x_5339_ = v___x_5328_;
                    v_isShared_5340_ = v_isSharedCheck_5356_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5337_);
                    lean_inc(v_infoState_5336_);
                    lean_inc(v_messages_5335_);
                    lean_inc(v_cache_5334_);
                    lean_inc(v_traceState_5329_);
                    lean_inc(v_auxDeclNGen_5333_);
                    lean_inc(v_ngen_5332_);
                    lean_inc(v_nextMacroScope_5331_);
                    lean_inc(v_env_5330_);
                    lean_dec(v___x_5328_);
                    v___x_5339_ = lean_box(0);
                    v_isShared_5340_ = v_isSharedCheck_5356_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_5341_ = lean_ctor_get_uint64(
                    v_traceState_5329_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5354_ = (!lean_is_exclusive(v_traceState_5329_)) as u8;
                if v_isSharedCheck_5354_ == 0 {
                    v_unused_5355_ = lean_ctor_get(v_traceState_5329_, 0);
                    lean_dec(v_unused_5355_);
                    v___x_5343_ = v_traceState_5329_;
                    v_isShared_5344_ = v_isSharedCheck_5354_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_traceState_5329_);
                    v___x_5343_ = lean_box(0);
                    v_isShared_5344_ = v_isSharedCheck_5354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5345_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___closed__1);
                if v_isShared_5344_ == 0 {
                    lean_ctor_set(v___x_5343_, 0, v___x_5345_);
                    v___x_5347_ = v___x_5343_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5345_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5353_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5341_,
                    );
                    v___x_5347_ = v_reuseFailAlloc_5353_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5340_ == 0 {
                    lean_ctor_set(v___x_5339_, 4, v___x_5347_);
                    v___x_5349_ = v___x_5339_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_env_5330_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 1, v_nextMacroScope_5331_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 2, v_ngen_5332_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 3, v_auxDeclNGen_5333_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 4, v___x_5347_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 5, v_cache_5334_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 6, v_messages_5335_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 7, v_infoState_5336_);
                    lean_ctor_set(v_reuseFailAlloc_5352_, 8, v_snapshotTasks_5337_);
                    v___x_5349_ = v_reuseFailAlloc_5352_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5350_ = lean_st_ref_set(v___y_5323_, v___x_5349_);
                v___x_5351_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5351_, 0, v_traces_5327_);
                return v___x_5351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg___boxed(
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5359_: *mut LeanObject = core::ptr::null_mut();
    v_res_5359_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_5357_);
    lean_dec(v___y_5357_);
    return v_res_5359_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(
    mut v___y_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    v___x_5365_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v___y_5363_);
    return v___x_5365_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___boxed(
    mut v___y_5366_: *mut LeanObject,
    mut v___y_5367_: *mut LeanObject,
    mut v___y_5368_: *mut LeanObject,
    mut v___y_5369_: *mut LeanObject,
    mut v___y_5370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5371_: *mut LeanObject = core::ptr::null_mut();
    v_res_5371_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5(v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_);
    lean_dec(v___y_5369_);
    lean_dec_ref(v___y_5368_);
    lean_dec(v___y_5367_);
    lean_dec_ref(v___y_5366_);
    return v_res_5371_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(
    mut v_opts_5372_: *mut LeanObject,
    mut v_opt_5373_: *mut LeanObject,
) -> u8 {
    let mut v_name_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    v_name_5374_ = lean_ctor_get(v_opt_5373_, 0);
    v_defValue_5375_ = lean_ctor_get(v_opt_5373_, 1);
    v_map_5376_ = lean_ctor_get(v_opts_5372_, 0);
    v___x_5377_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5376_,
            v_name_5374_,
        );
    if lean_obj_tag(v___x_5377_) == 0 {
        let mut v___x_5378_: u8 = 0;
        v___x_5378_ = (lean_unbox(v_defValue_5375_) as u8);
        return v___x_5378_;
    } else {
        let mut v_val_5379_: *mut LeanObject = core::ptr::null_mut();
        v_val_5379_ = lean_ctor_get(v___x_5377_, 0);
        lean_inc(v_val_5379_);
        lean_dec_ref_known(v___x_5377_, 1);
        if lean_obj_tag(v_val_5379_) == 1 {
            let mut v_v_5380_: u8 = 0;
            v_v_5380_ = lean_ctor_get_uint8(v_val_5379_, 0 as u32);
            lean_dec_ref_known(v_val_5379_, 0);
            return v_v_5380_;
        } else {
            let mut v___x_5381_: u8 = 0;
            lean_dec(v_val_5379_);
            v___x_5381_ = (lean_unbox(v_defValue_5375_) as u8);
            return v___x_5381_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6___boxed(
    mut v_opts_5382_: *mut LeanObject,
    mut v_opt_5383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5384_: u8 = 0;
    let mut v_r_5385_: *mut LeanObject = core::ptr::null_mut();
    v_res_5384_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_5382_, v_opt_5383_);
    lean_dec_ref(v_opt_5383_);
    lean_dec_ref(v_opts_5382_);
    v_r_5385_ = lean_box((v_res_5384_) as usize);
    return v_r_5385_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    v___x_5387_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__0;
    v___x_5388_ = l_Lean_stringToMessageData(v___x_5387_);
    return v___x_5388_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    v___x_5390_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__2;
    v___x_5391_ = l_Lean_stringToMessageData(v___x_5390_);
    return v___x_5391_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    v___x_5393_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__4;
    v___x_5394_ = l_Lean_stringToMessageData(v___x_5393_);
    return v___x_5394_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(
    mut v_candidate_5395_: *mut LeanObject,
    mut v_t_5396_: *mut LeanObject,
    mut v_s_5397_: *mut LeanObject,
    mut v_x_5398_: *mut LeanObject,
    mut v___y_5399_: *mut LeanObject,
    mut v___y_5400_: *mut LeanObject,
    mut v___y_5401_: *mut LeanObject,
    mut v___y_5402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    v___x_5404_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__1);
    v___x_5405_ = l_Lean_MessageData_ofName(v_candidate_5395_);
    v___x_5406_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5406_, 0, v___x_5404_);
    lean_ctor_set(v___x_5406_, 1, v___x_5405_);
    v___x_5407_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__3);
    v___x_5408_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5408_, 0, v___x_5406_);
    lean_ctor_set(v___x_5408_, 1, v___x_5407_);
    v___x_5409_ = l_Lean_MessageData_ofExpr(v_t_5396_);
    v___x_5410_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5410_, 0, v___x_5408_);
    lean_ctor_set(v___x_5410_, 1, v___x_5409_);
    v___x_5411_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
    v___x_5412_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5412_, 0, v___x_5410_);
    lean_ctor_set(v___x_5412_, 1, v___x_5411_);
    v___x_5413_ = l_Lean_MessageData_ofExpr(v_s_5397_);
    v___x_5414_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5414_, 0, v___x_5412_);
    lean_ctor_set(v___x_5414_, 1, v___x_5413_);
    v___x_5415_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5415_, 0, v___x_5414_);
    return v___x_5415_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed(
    mut v_candidate_5416_: *mut LeanObject,
    mut v_t_5417_: *mut LeanObject,
    mut v_s_5418_: *mut LeanObject,
    mut v_x_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
    mut v___y_5423_: *mut LeanObject,
    mut v___y_5424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5425_: *mut LeanObject = core::ptr::null_mut();
    v_res_5425_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0(v_candidate_5416_, v_t_5417_, v_s_5418_, v_x_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
    lean_dec(v___y_5423_);
    lean_dec_ref(v___y_5422_);
    lean_dec(v___y_5421_);
    lean_dec_ref(v___y_5420_);
    lean_dec_ref(v_x_5419_);
    return v_res_5425_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(
    mut v_e_5426_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_e_5426_) == 0 {
        let mut v___x_5427_: u8 = 0;
        v___x_5427_ = 2;
        return v___x_5427_;
    } else {
        let mut v_a_5428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5429_: u8 = 0;
        v_a_5428_ = lean_ctor_get(v_e_5426_, 0);
        v___x_5429_ = (lean_unbox(v_a_5428_) as u8);
        if v___x_5429_ == 0 {
            let mut v___x_5430_: u8 = 0;
            v___x_5430_ = 1;
            return v___x_5430_;
        } else {
            let mut v___x_5431_: u8 = 0;
            v___x_5431_ = 0;
            return v___x_5431_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7___boxed(
    mut v_e_5432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5433_: u8 = 0;
    let mut v_r_5434_: *mut LeanObject = core::ptr::null_mut();
    v_res_5433_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_e_5432_);
    lean_dec_ref(v_e_5432_);
    v_r_5434_ = lean_box((v_res_5433_) as usize);
    return v_r_5434_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(
    mut v_opts_5435_: *mut LeanObject,
    mut v_opt_5436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    v_name_5437_ = lean_ctor_get(v_opt_5436_, 0);
    v_defValue_5438_ = lean_ctor_get(v_opt_5436_, 1);
    v_map_5439_ = lean_ctor_get(v_opts_5435_, 0);
    v___x_5440_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5439_,
            v_name_5437_,
        );
    if lean_obj_tag(v___x_5440_) == 0 {
        lean_inc(v_defValue_5438_);
        return v_defValue_5438_;
    } else {
        let mut v_val_5441_: *mut LeanObject = core::ptr::null_mut();
        v_val_5441_ = lean_ctor_get(v___x_5440_, 0);
        lean_inc(v_val_5441_);
        lean_dec_ref_known(v___x_5440_, 1);
        if lean_obj_tag(v_val_5441_) == 3 {
            let mut v_v_5442_: *mut LeanObject = core::ptr::null_mut();
            v_v_5442_ = lean_ctor_get(v_val_5441_, 0);
            lean_inc(v_v_5442_);
            lean_dec_ref_known(v_val_5441_, 1);
            return v_v_5442_;
        } else {
            lean_dec(v_val_5441_);
            lean_inc(v_defValue_5438_);
            return v_defValue_5438_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10___boxed(
    mut v_opts_5443_: *mut LeanObject,
    mut v_opt_5444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5445_: *mut LeanObject = core::ptr::null_mut();
    v_res_5445_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_5443_, v_opt_5444_);
    lean_dec_ref(v_opt_5444_);
    lean_dec_ref(v_opts_5443_);
    return v_res_5445_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(
    mut v_x_5446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5455_: u8 = 0;
    let mut v_a_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5446_) == 0 {
                    v_a_5448_ = lean_ctor_get(v_x_5446_, 0);
                    v_isSharedCheck_5455_ = (!lean_is_exclusive(v_x_5446_)) as u8;
                    if v_isSharedCheck_5455_ == 0 {
                        v___x_5450_ = v_x_5446_;
                        v_isShared_5451_ = v_isSharedCheck_5455_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5448_);
                        lean_dec(v_x_5446_);
                        v___x_5450_ = lean_box(0);
                        v_isShared_5451_ = v_isSharedCheck_5455_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5456_ = lean_ctor_get(v_x_5446_, 0);
                    v_isSharedCheck_5463_ = (!lean_is_exclusive(v_x_5446_)) as u8;
                    if v_isSharedCheck_5463_ == 0 {
                        v___x_5458_ = v_x_5446_;
                        v_isShared_5459_ = v_isSharedCheck_5463_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5456_);
                        lean_dec(v_x_5446_);
                        v___x_5458_ = lean_box(0);
                        v_isShared_5459_ = v_isSharedCheck_5463_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5451_ == 0 {
                    lean_ctor_set_tag(v___x_5450_, 1);
                    v___x_5453_ = v___x_5450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_a_5448_);
                    v___x_5453_ = v_reuseFailAlloc_5454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5453_;
            }
            3 => {
                if v_isShared_5459_ == 0 {
                    lean_ctor_set_tag(v___x_5458_, 0);
                    v___x_5461_ = v___x_5458_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
                    v___x_5461_ = v_reuseFailAlloc_5462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg___boxed(
    mut v_x_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5466_: *mut LeanObject = core::ptr::null_mut();
    v_res_5466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_5464_);
    return v_res_5466_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(
    mut v_sz_5467_: usize,
    mut v_i_5468_: usize,
    mut v_bs_5469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5470_: u8 = 0;
    let mut v_v_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: usize = 0;
    let mut v___x_5476_: usize = 0;
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5470_ = lean_usize_dec_lt(v_i_5468_, v_sz_5467_);
                if v___x_5470_ == 0 {
                    return v_bs_5469_;
                } else {
                    v_v_5471_ = lean_array_uget_borrowed(v_bs_5469_, v_i_5468_);
                    v_msg_5472_ = lean_ctor_get(v_v_5471_, 1);
                    lean_inc_ref(v_msg_5472_);
                    v___x_5473_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5474_ = lean_array_uset(v_bs_5469_, v_i_5468_, v___x_5473_);
                    v___x_5475_ = 1usize;
                    v___x_5476_ = lean_usize_add(v_i_5468_, v___x_5475_);
                    v___x_5477_ = lean_array_uset(v_bs_x27_5474_, v_i_5468_, v_msg_5472_);
                    v_i_5468_ = v___x_5476_;
                    v_bs_5469_ = v___x_5477_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9___boxed(
    mut v_sz_5479_: *mut LeanObject,
    mut v_i_5480_: *mut LeanObject,
    mut v_bs_5481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5482_: usize = 0;
    let mut v_i_boxed_5483_: usize = 0;
    let mut v_res_5484_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5482_ = lean_unbox_usize(v_sz_5479_);
    lean_dec(v_sz_5479_);
    v_i_boxed_5483_ = lean_unbox_usize(v_i_5480_);
    lean_dec(v_i_5480_);
    v_res_5484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_boxed_5482_, v_i_boxed_5483_, v_bs_5481_);
    return v_res_5484_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(
    mut v_oldTraces_5485_: *mut LeanObject,
    mut v_data_5486_: *mut LeanObject,
    mut v_ref_5487_: *mut LeanObject,
    mut v_msg_5488_: *mut LeanObject,
    mut v___y_5489_: *mut LeanObject,
    mut v___y_5490_: *mut LeanObject,
    mut v___y_5491_: *mut LeanObject,
    mut v___y_5492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5506_: u8 = 0;
    let mut v_cancelTk_x3f_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5508_: u8 = 0;
    let mut v_inheritedTraceOptions_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5516_: usize = 0;
    let mut v___x_5517_: usize = 0;
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5537_: u8 = 0;
    let mut v_tid_5538_: u64 = 0;
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5541_: u8 = 0;
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v_unused_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut v_isSharedCheck_5558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5494_ = lean_ctor_get(v___y_5491_, 0);
                v_fileMap_5495_ = lean_ctor_get(v___y_5491_, 1);
                v_options_5496_ = lean_ctor_get(v___y_5491_, 2);
                v_currRecDepth_5497_ = lean_ctor_get(v___y_5491_, 3);
                v_maxRecDepth_5498_ = lean_ctor_get(v___y_5491_, 4);
                v_ref_5499_ = lean_ctor_get(v___y_5491_, 5);
                v_currNamespace_5500_ = lean_ctor_get(v___y_5491_, 6);
                v_openDecls_5501_ = lean_ctor_get(v___y_5491_, 7);
                v_initHeartbeats_5502_ = lean_ctor_get(v___y_5491_, 8);
                v_maxHeartbeats_5503_ = lean_ctor_get(v___y_5491_, 9);
                v_quotContext_5504_ = lean_ctor_get(v___y_5491_, 10);
                v_currMacroScope_5505_ = lean_ctor_get(v___y_5491_, 11);
                v_diag_5506_ = lean_ctor_get_uint8(
                    v___y_5491_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5507_ = lean_ctor_get(v___y_5491_, 12);
                v_suppressElabErrors_5508_ = lean_ctor_get_uint8(
                    v___y_5491_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5509_ = lean_ctor_get(v___y_5491_, 13);
                v___x_5510_ = lean_st_ref_get(v___y_5492_);
                v_traceState_5511_ = lean_ctor_get(v___x_5510_, 4);
                lean_inc_ref(v_traceState_5511_);
                lean_dec(v___x_5510_);
                v_traces_5512_ = lean_ctor_get(v_traceState_5511_, 0);
                lean_inc_ref(v_traces_5512_);
                lean_dec_ref(v_traceState_5511_);
                v_ref_5513_ = l_Lean_replaceRef(v_ref_5487_, v_ref_5499_);
                lean_inc_ref(v_inheritedTraceOptions_5509_);
                lean_inc(v_cancelTk_x3f_5507_);
                lean_inc(v_currMacroScope_5505_);
                lean_inc(v_quotContext_5504_);
                lean_inc(v_maxHeartbeats_5503_);
                lean_inc(v_initHeartbeats_5502_);
                lean_inc(v_openDecls_5501_);
                lean_inc(v_currNamespace_5500_);
                lean_inc(v_maxRecDepth_5498_);
                lean_inc(v_currRecDepth_5497_);
                lean_inc_ref(v_options_5496_);
                lean_inc_ref(v_fileMap_5495_);
                lean_inc_ref(v_fileName_5494_);
                v___x_5514_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5514_, 0, v_fileName_5494_);
                lean_ctor_set(v___x_5514_, 1, v_fileMap_5495_);
                lean_ctor_set(v___x_5514_, 2, v_options_5496_);
                lean_ctor_set(v___x_5514_, 3, v_currRecDepth_5497_);
                lean_ctor_set(v___x_5514_, 4, v_maxRecDepth_5498_);
                lean_ctor_set(v___x_5514_, 5, v_ref_5513_);
                lean_ctor_set(v___x_5514_, 6, v_currNamespace_5500_);
                lean_ctor_set(v___x_5514_, 7, v_openDecls_5501_);
                lean_ctor_set(v___x_5514_, 8, v_initHeartbeats_5502_);
                lean_ctor_set(v___x_5514_, 9, v_maxHeartbeats_5503_);
                lean_ctor_set(v___x_5514_, 10, v_quotContext_5504_);
                lean_ctor_set(v___x_5514_, 11, v_currMacroScope_5505_);
                lean_ctor_set(v___x_5514_, 12, v_cancelTk_x3f_5507_);
                lean_ctor_set(v___x_5514_, 13, v_inheritedTraceOptions_5509_);
                lean_ctor_set_uint8(
                    v___x_5514_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_5506_,
                );
                lean_ctor_set_uint8(
                    v___x_5514_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5508_,
                );
                v___x_5515_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5512_);
                lean_dec_ref(v_traces_5512_);
                v_sz_5516_ = lean_array_size(v___x_5515_);
                v___x_5517_ = 0usize;
                v___x_5518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8_spec__9(v_sz_5516_, v___x_5517_, v___x_5515_);
                v_msg_5519_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v_msg_5519_, 0, v_data_5486_);
                lean_ctor_set(v_msg_5519_, 1, v_msg_5488_);
                lean_ctor_set(v_msg_5519_, 2, v___x_5518_);
                v___x_5520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_validateHint_spec__0_spec__0(v_msg_5519_, v___y_5489_, v___y_5490_, v___x_5514_, v___y_5492_);
                lean_dec_ref_known(v___x_5514_, 14);
                v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
                v_isSharedCheck_5558_ = (!lean_is_exclusive(v___x_5520_)) as u8;
                if v_isSharedCheck_5558_ == 0 {
                    v___x_5523_ = v___x_5520_;
                    v_isShared_5524_ = v_isSharedCheck_5558_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5521_);
                    lean_dec(v___x_5520_);
                    v___x_5523_ = lean_box(0);
                    v_isShared_5524_ = v_isSharedCheck_5558_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5525_ = lean_st_ref_take(v___y_5492_);
                v_traceState_5526_ = lean_ctor_get(v___x_5525_, 4);
                v_env_5527_ = lean_ctor_get(v___x_5525_, 0);
                v_nextMacroScope_5528_ = lean_ctor_get(v___x_5525_, 1);
                v_ngen_5529_ = lean_ctor_get(v___x_5525_, 2);
                v_auxDeclNGen_5530_ = lean_ctor_get(v___x_5525_, 3);
                v_cache_5531_ = lean_ctor_get(v___x_5525_, 5);
                v_messages_5532_ = lean_ctor_get(v___x_5525_, 6);
                v_infoState_5533_ = lean_ctor_get(v___x_5525_, 7);
                v_snapshotTasks_5534_ = lean_ctor_get(v___x_5525_, 8);
                v_isSharedCheck_5557_ = (!lean_is_exclusive(v___x_5525_)) as u8;
                if v_isSharedCheck_5557_ == 0 {
                    v___x_5536_ = v___x_5525_;
                    v_isShared_5537_ = v_isSharedCheck_5557_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5534_);
                    lean_inc(v_infoState_5533_);
                    lean_inc(v_messages_5532_);
                    lean_inc(v_cache_5531_);
                    lean_inc(v_traceState_5526_);
                    lean_inc(v_auxDeclNGen_5530_);
                    lean_inc(v_ngen_5529_);
                    lean_inc(v_nextMacroScope_5528_);
                    lean_inc(v_env_5527_);
                    lean_dec(v___x_5525_);
                    v___x_5536_ = lean_box(0);
                    v_isShared_5537_ = v_isSharedCheck_5557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5538_ = lean_ctor_get_uint64(
                    v_traceState_5526_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5555_ = (!lean_is_exclusive(v_traceState_5526_)) as u8;
                if v_isSharedCheck_5555_ == 0 {
                    v_unused_5556_ = lean_ctor_get(v_traceState_5526_, 0);
                    lean_dec(v_unused_5556_);
                    v___x_5540_ = v_traceState_5526_;
                    v_isShared_5541_ = v_isSharedCheck_5555_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_traceState_5526_);
                    v___x_5540_ = lean_box(0);
                    v_isShared_5541_ = v_isSharedCheck_5555_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5542_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5542_, 0, v_ref_5487_);
                lean_ctor_set(v___x_5542_, 1, v_a_5521_);
                v___x_5543_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5485_, v___x_5542_);
                if v_isShared_5541_ == 0 {
                    lean_ctor_set(v___x_5540_, 0, v___x_5543_);
                    v___x_5545_ = v___x_5540_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5554_, 0, v___x_5543_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5554_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5538_,
                    );
                    v___x_5545_ = v_reuseFailAlloc_5554_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5537_ == 0 {
                    lean_ctor_set(v___x_5536_, 4, v___x_5545_);
                    v___x_5547_ = v___x_5536_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_env_5527_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 1, v_nextMacroScope_5528_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 2, v_ngen_5529_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 3, v_auxDeclNGen_5530_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 4, v___x_5545_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 5, v_cache_5531_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 6, v_messages_5532_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 7, v_infoState_5533_);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 8, v_snapshotTasks_5534_);
                    v___x_5547_ = v_reuseFailAlloc_5553_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5548_ = lean_st_ref_set(v___y_5492_, v___x_5547_);
                v___x_5549_ = lean_box(0);
                if v_isShared_5524_ == 0 {
                    lean_ctor_set(v___x_5523_, 0, v___x_5549_);
                    v___x_5551_ = v___x_5523_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5552_, 0, v___x_5549_);
                    v___x_5551_ = v_reuseFailAlloc_5552_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8___boxed(
    mut v_oldTraces_5559_: *mut LeanObject,
    mut v_data_5560_: *mut LeanObject,
    mut v_ref_5561_: *mut LeanObject,
    mut v_msg_5562_: *mut LeanObject,
    mut v___y_5563_: *mut LeanObject,
    mut v___y_5564_: *mut LeanObject,
    mut v___y_5565_: *mut LeanObject,
    mut v___y_5566_: *mut LeanObject,
    mut v___y_5567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5568_: *mut LeanObject = core::ptr::null_mut();
    v_res_5568_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_5559_, v_data_5560_, v_ref_5561_, v_msg_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
    lean_dec(v___y_5566_);
    lean_dec_ref(v___y_5565_);
    lean_dec(v___y_5564_);
    lean_dec_ref(v___y_5563_);
    return v_res_5568_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1()
-> *mut LeanObject {
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    v___x_5570_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__0;
    v___x_5571_ = l_Lean_stringToMessageData(v___x_5570_);
    return v___x_5571_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3()
-> *mut LeanObject {
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    v___x_5573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__2;
    v___x_5574_ = l_Lean_stringToMessageData(v___x_5573_);
    return v___x_5574_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4()
-> f64 {
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: f64 = 0.0;
    v___x_5575_ = lean_unsigned_to_nat(1000);
    v___x_5576_ = lean_float_of_nat(v___x_5575_);
    return v___x_5576_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(
    mut v_cls_5577_: *mut LeanObject,
    mut v_collapsed_5578_: u8,
    mut v_tag_5579_: *mut LeanObject,
    mut v_opts_5580_: *mut LeanObject,
    mut v_clsEnabled_5581_: u8,
    mut v_oldTraces_5582_: *mut LeanObject,
    mut v_msg_5583_: *mut LeanObject,
    mut v_resStartStop_5584_: *mut LeanObject,
    mut v___y_5585_: *mut LeanObject,
    mut v___y_5586_: *mut LeanObject,
    mut v___y_5587_: *mut LeanObject,
    mut v___y_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___y_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5604_: u8 = 0;
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5608_: u8 = 0;
    let mut v_fst_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5613_: u8 = 0;
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: u8 = 0;
    let mut v___y_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_5619_: u8 = 0;
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: f64 = 0.0;
    let mut v_data_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: f64 = 0.0;
    let mut v___x_5633_: f64 = 0.0;
    let mut v_reuseFailAlloc_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5642_: u8 = 0;
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5655_: u8 = 0;
    let mut v_tid_5656_: u64 = 0;
    let mut v_traces_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5660_: u8 = 0;
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5670_: u8 = 0;
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut v___y_5673_: f64 = 0.0;
    let mut v___x_5674_: f64 = 0.0;
    let mut v___x_5675_: f64 = 0.0;
    let mut v___x_5676_: f64 = 0.0;
    let mut v___x_5677_: u8 = 0;
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: u8 = 0;
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: f64 = 0.0;
    let mut v___x_5683_: f64 = 0.0;
    let mut v___x_5684_: f64 = 0.0;
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: f64 = 0.0;
    let mut v_isSharedCheck_5688_: u8 = 0;
    let mut v_isSharedCheck_5689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5590_ = lean_ctor_get(v_resStartStop_5584_, 0);
                v_snd_5591_ = lean_ctor_get(v_resStartStop_5584_, 1);
                v_isSharedCheck_5689_ = (!lean_is_exclusive(v_resStartStop_5584_)) as u8;
                if v_isSharedCheck_5689_ == 0 {
                    v___x_5593_ = v_resStartStop_5584_;
                    v_isShared_5594_ = v_isSharedCheck_5689_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5591_);
                    lean_inc(v_fst_5590_);
                    lean_dec(v_resStartStop_5584_);
                    v___x_5593_ = lean_box(0);
                    v_isShared_5594_ = v_isSharedCheck_5689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5609_ = lean_ctor_get(v_snd_5591_, 0);
                v_snd_5610_ = lean_ctor_get(v_snd_5591_, 1);
                v_isSharedCheck_5688_ = (!lean_is_exclusive(v_snd_5591_)) as u8;
                if v_isSharedCheck_5688_ == 0 {
                    v___x_5612_ = v_snd_5591_;
                    v_isShared_5613_ = v_isSharedCheck_5688_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_5610_);
                    lean_inc(v_fst_5609_);
                    lean_dec(v_snd_5591_);
                    v___x_5612_ = lean_box(0);
                    v_isShared_5613_ = v_isSharedCheck_5688_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_5597_);
                v___x_5599_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__8(v_oldTraces_5582_, v_data_5598_, v___y_5597_, v___y_5596_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_);
                if lean_obj_tag(v___x_5599_) == 0 {
                    lean_dec_ref_known(v___x_5599_, 1);
                    v___x_5600_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_5590_);
                    return v___x_5600_;
                } else {
                    lean_dec(v_fst_5590_);
                    v_a_5601_ = lean_ctor_get(v___x_5599_, 0);
                    v_isSharedCheck_5608_ = (!lean_is_exclusive(v___x_5599_)) as u8;
                    if v_isSharedCheck_5608_ == 0 {
                        v___x_5603_ = v___x_5599_;
                        v_isShared_5604_ = v_isSharedCheck_5608_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5601_);
                        lean_dec(v___x_5599_);
                        v___x_5603_ = lean_box(0);
                        v_isShared_5604_ = v_isSharedCheck_5608_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5604_ == 0 {
                    v___x_5606_ = v___x_5603_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5601_);
                    v___x_5606_ = v_reuseFailAlloc_5607_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5606_;
            }
            5 => {
                v___x_5614_ = l_Lean_trace_profiler;
                v___x_5615_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_5580_, v___x_5614_);
                if v___x_5615_ == 0 {
                    v___y_5642_ = v___x_5615_;
                    state = 10;
                    continue;
                } else {
                    v___x_5678_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_5679_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_opts_5580_, v___x_5678_);
                    if v___x_5679_ == 0 {
                        v___x_5680_ = l_Lean_trace_profiler_threshold;
                        v___x_5681_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_5580_, v___x_5680_);
                        v___x_5682_ = lean_float_of_nat(v___x_5681_);
                        v___x_5683_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__4);
                        v___x_5684_ = lean_float_div(v___x_5682_, v___x_5683_);
                        v___y_5673_ = v___x_5684_;
                        state = 15;
                        continue;
                    } else {
                        v___x_5685_ = l_Lean_trace_profiler_threshold;
                        v___x_5686_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__10(v_opts_5580_, v___x_5685_);
                        v___x_5687_ = lean_float_of_nat(v___x_5686_);
                        v___y_5673_ = v___x_5687_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_5619_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__7(v_fst_5590_);
                v___x_5620_ = l_Lean_TraceResult_toEmoji(v_result_5619_);
                v___x_5621_ = l_Lean_stringToMessageData(v___x_5620_);
                v___x_5622_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__1);
                if v_isShared_5613_ == 0 {
                    lean_ctor_set_tag(v___x_5612_, 7);
                    lean_ctor_set(v___x_5612_, 1, v___x_5622_);
                    lean_ctor_set(v___x_5612_, 0, v___x_5621_);
                    v___x_5624_ = v___x_5612_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5635_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5635_, 0, v___x_5621_);
                    lean_ctor_set(v_reuseFailAlloc_5635_, 1, v___x_5622_);
                    v___x_5624_ = v_reuseFailAlloc_5635_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5594_ == 0 {
                    lean_ctor_set_tag(v___x_5593_, 7);
                    lean_ctor_set(v___x_5593_, 1, v_a_5618_);
                    lean_ctor_set(v___x_5593_, 0, v___x_5624_);
                    v_m_5626_ = v___x_5593_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5634_, 0, v___x_5624_);
                    lean_ctor_set(v_reuseFailAlloc_5634_, 1, v_a_5618_);
                    v_m_5626_ = v_reuseFailAlloc_5634_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5627_ = lean_box((v_result_5619_) as usize);
                v___x_5628_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5628_, 0, v___x_5627_);
                v___x_5629_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__0);
                lean_inc_ref(v_tag_5579_);
                lean_inc_ref(v___x_5628_);
                lean_inc(v_cls_5577_);
                v_data_5630_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_5630_, 0, v_cls_5577_);
                lean_ctor_set(v_data_5630_, 1, v___x_5628_);
                lean_ctor_set(v_data_5630_, 2, v_tag_5579_);
                lean_ctor_set_float(
                    v_data_5630_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5629_,
                );
                lean_ctor_set_float(
                    v_data_5630_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5629_,
                );
                lean_ctor_set_uint8(
                    v_data_5630_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_5578_,
                );
                if v___x_5615_ == 0 {
                    lean_dec_ref_known(v___x_5628_, 1);
                    lean_dec(v_snd_5610_);
                    lean_dec(v_fst_5609_);
                    lean_dec_ref(v_tag_5579_);
                    lean_dec(v_cls_5577_);
                    v___y_5596_ = v_m_5626_;
                    v___y_5597_ = v___y_5617_;
                    v_data_5598_ = v_data_5630_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_5630_, 3);
                    v_data_5631_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_5631_, 0, v_cls_5577_);
                    lean_ctor_set(v_data_5631_, 1, v___x_5628_);
                    lean_ctor_set(v_data_5631_, 2, v_tag_5579_);
                    v___x_5632_ = lean_unbox_float(v_fst_5609_);
                    lean_dec(v_fst_5609_);
                    lean_ctor_set_float(
                        v_data_5631_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_5632_,
                    );
                    v___x_5633_ = lean_unbox_float(v_snd_5610_);
                    lean_dec(v_snd_5610_);
                    lean_ctor_set_float(
                        v_data_5631_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_5633_,
                    );
                    lean_ctor_set_uint8(
                        v_data_5631_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_collapsed_5578_,
                    );
                    v___y_5596_ = v_m_5626_;
                    v___y_5597_ = v___y_5617_;
                    v_data_5598_ = v_data_5631_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_5637_ = lean_ctor_get(v___y_5587_, 5);
                lean_inc(v___y_5588_);
                lean_inc_ref(v___y_5587_);
                lean_inc(v___y_5586_);
                lean_inc_ref(v___y_5585_);
                lean_inc(v_fst_5590_);
                v___x_5638_ = lean_apply_6(
                    v_msg_5583_,
                    v_fst_5590_,
                    v___y_5585_,
                    v___y_5586_,
                    v___y_5587_,
                    v___y_5588_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5638_) == 0 {
                    v_a_5639_ = lean_ctor_get(v___x_5638_, 0);
                    lean_inc(v_a_5639_);
                    lean_dec_ref_known(v___x_5638_, 1);
                    v___y_5617_ = v_ref_5637_;
                    v_a_5618_ = v_a_5639_;
                    state = 6;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_5638_, 1);
                    v___x_5640_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___closed__3);
                    v___y_5617_ = v_ref_5637_;
                    v_a_5618_ = v___x_5640_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_5581_ == 0 {
                    if v___y_5642_ == 0 {
                        lean_del_object(v___x_5612_);
                        lean_dec(v_snd_5610_);
                        lean_dec(v_fst_5609_);
                        lean_del_object(v___x_5593_);
                        lean_dec_ref(v_msg_5583_);
                        lean_dec_ref(v_tag_5579_);
                        lean_dec(v_cls_5577_);
                        v___x_5643_ = lean_st_ref_take(v___y_5588_);
                        v_traceState_5644_ = lean_ctor_get(v___x_5643_, 4);
                        v_env_5645_ = lean_ctor_get(v___x_5643_, 0);
                        v_nextMacroScope_5646_ = lean_ctor_get(v___x_5643_, 1);
                        v_ngen_5647_ = lean_ctor_get(v___x_5643_, 2);
                        v_auxDeclNGen_5648_ = lean_ctor_get(v___x_5643_, 3);
                        v_cache_5649_ = lean_ctor_get(v___x_5643_, 5);
                        v_messages_5650_ = lean_ctor_get(v___x_5643_, 6);
                        v_infoState_5651_ = lean_ctor_get(v___x_5643_, 7);
                        v_snapshotTasks_5652_ = lean_ctor_get(v___x_5643_, 8);
                        v_isSharedCheck_5671_ = (!lean_is_exclusive(v___x_5643_)) as u8;
                        if v_isSharedCheck_5671_ == 0 {
                            v___x_5654_ = v___x_5643_;
                            v_isShared_5655_ = v_isSharedCheck_5671_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_5652_);
                            lean_inc(v_infoState_5651_);
                            lean_inc(v_messages_5650_);
                            lean_inc(v_cache_5649_);
                            lean_inc(v_traceState_5644_);
                            lean_inc(v_auxDeclNGen_5648_);
                            lean_inc(v_ngen_5647_);
                            lean_inc(v_nextMacroScope_5646_);
                            lean_inc(v_env_5645_);
                            lean_dec(v___x_5643_);
                            v___x_5654_ = lean_box(0);
                            v_isShared_5655_ = v_isSharedCheck_5671_;
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
                v_tid_5656_ = lean_ctor_get_uint64(
                    v_traceState_5644_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5657_ = lean_ctor_get(v_traceState_5644_, 0);
                v_isSharedCheck_5670_ = (!lean_is_exclusive(v_traceState_5644_)) as u8;
                if v_isSharedCheck_5670_ == 0 {
                    v___x_5659_ = v_traceState_5644_;
                    v_isShared_5660_ = v_isSharedCheck_5670_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_traces_5657_);
                    lean_dec(v_traceState_5644_);
                    v___x_5659_ = lean_box(0);
                    v_isShared_5660_ = v_isSharedCheck_5670_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5661_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_5582_, v_traces_5657_);
                lean_dec_ref(v_traces_5657_);
                if v_isShared_5660_ == 0 {
                    lean_ctor_set(v___x_5659_, 0, v___x_5661_);
                    v___x_5663_ = v___x_5659_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5661_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5669_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5656_,
                    );
                    v___x_5663_ = v_reuseFailAlloc_5669_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5655_ == 0 {
                    lean_ctor_set(v___x_5654_, 4, v___x_5663_);
                    v___x_5665_ = v___x_5654_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_env_5645_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 1, v_nextMacroScope_5646_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 2, v_ngen_5647_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 3, v_auxDeclNGen_5648_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 4, v___x_5663_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 5, v_cache_5649_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 6, v_messages_5650_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 7, v_infoState_5651_);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 8, v_snapshotTasks_5652_);
                    v___x_5665_ = v_reuseFailAlloc_5668_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5666_ = lean_st_ref_set(v___y_5588_, v___x_5665_);
                v___x_5667_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_fst_5590_);
                return v___x_5667_;
            }
            15 => {
                v___x_5674_ = lean_unbox_float(v_snd_5610_);
                v___x_5675_ = lean_unbox_float(v_fst_5609_);
                v___x_5676_ = lean_float_sub(v___x_5674_, v___x_5675_);
                v___x_5677_ = lean_float_decLt(v___y_5673_, v___x_5676_);
                v___y_5642_ = v___x_5677_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7___boxed(
    mut v_cls_5690_: *mut LeanObject,
    mut v_collapsed_5691_: *mut LeanObject,
    mut v_tag_5692_: *mut LeanObject,
    mut v_opts_5693_: *mut LeanObject,
    mut v_clsEnabled_5694_: *mut LeanObject,
    mut v_oldTraces_5695_: *mut LeanObject,
    mut v_msg_5696_: *mut LeanObject,
    mut v_resStartStop_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5703_: u8 = 0;
    let mut v_clsEnabled_boxed_5704_: u8 = 0;
    let mut v_res_5705_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5703_ = (lean_unbox(v_collapsed_5691_) as u8);
    v_clsEnabled_boxed_5704_ = (lean_unbox(v_clsEnabled_5694_) as u8);
    v_res_5705_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_5690_, v_collapsed_boxed_5703_, v_tag_5692_, v_opts_5693_, v_clsEnabled_boxed_5704_, v_oldTraces_5695_, v_msg_5696_, v_resStartStop_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
    lean_dec(v___y_5701_);
    lean_dec_ref(v___y_5700_);
    lean_dec(v___y_5699_);
    lean_dec_ref(v___y_5698_);
    lean_dec_ref(v_opts_5693_);
    return v_res_5705_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0()
-> f64 {
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: f64 = 0.0;
    v___x_5706_ = lean_unsigned_to_nat(1000000000);
    v___x_5707_ = lean_float_of_nat(v___x_5706_);
    return v___x_5707_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(
    mut v_t_5708_: *mut LeanObject,
    mut v_s_5709_: *mut LeanObject,
    mut v_candidate_5710_: *mut LeanObject,
    mut v_a_5711_: *mut LeanObject,
    mut v_a_5712_: *mut LeanObject,
    mut v_a_5713_: *mut LeanObject,
    mut v_a_5714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5718_: u8 = 0;
    let mut v___x_5719_: u8 = 0;
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: u8 = 0;
    let mut v___y_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: f64 = 0.0;
    let mut v___x_5732_: f64 = 0.0;
    let mut v___x_5733_: f64 = 0.0;
    let mut v___x_5734_: f64 = 0.0;
    let mut v___x_5735_: f64 = 0.0;
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: f64 = 0.0;
    let mut v___x_5747_: f64 = 0.0;
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: u8 = 0;
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5763_: u8 = 0;
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5767_: u8 = 0;
    let mut v_a_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5771_: u8 = 0;
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5775_: u8 = 0;
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5781_: u8 = 0;
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5785_: u8 = 0;
    let mut v_a_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5789_: u8 = 0;
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5793_: u8 = 0;
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: u8 = 0;
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5716_ = lean_ctor_get(v_a_5713_, 2);
                v_inheritedTraceOptions_5717_ = lean_ctor_get(v_a_5713_, 13);
                v_hasTrace_5718_ = lean_ctor_get_uint8(
                    v_options_5716_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_5719_ = 1;
                if v_hasTrace_5718_ == 0 {
                    v___x_5720_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_5710_, v_t_5708_, v_s_5709_, v___x_5719_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_);
                    return v___x_5720_;
                } else {
                    lean_inc_ref(v_s_5709_);
                    lean_inc_ref(v_t_5708_);
                    lean_inc(v_candidate_5710_);
                    v___f_5721_ = lean_alloc_closure(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                    lean_closure_set(v___f_5721_, 0, v_candidate_5710_);
                    lean_closure_set(v___f_5721_, 1, v_t_5708_);
                    lean_closure_set(v___f_5721_, 2, v_s_5709_);
                    v_cls_5722_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5;
                    v___x_5723_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3___closed__1;
                    v___x_5724_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once), _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
                    v___x_5725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5717_,
                        v_options_5716_,
                        v___x_5724_,
                    );
                    if v___x_5725_ == 0 {
                        v___x_5794_ = l_Lean_trace_profiler;
                        v___x_5795_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_5716_, v___x_5794_);
                        if v___x_5795_ == 0 {
                            lean_dec_ref(v___f_5721_);
                            v___x_5796_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_5710_, v_t_5708_, v_s_5709_, v___x_5719_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_);
                            return v___x_5796_;
                        } else {
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5730_ = lean_io_mono_nanos_now();
                v___x_5731_ = lean_float_of_nat(v___y_5728_);
                v___x_5732_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___closed__0);
                v___x_5733_ = lean_float_div(v___x_5731_, v___x_5732_);
                v___x_5734_ = lean_float_of_nat(v___x_5730_);
                v___x_5735_ = lean_float_div(v___x_5734_, v___x_5732_);
                v___x_5736_ = lean_box_float(v___x_5733_);
                v___x_5737_ = lean_box_float(v___x_5735_);
                v___x_5738_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5738_, 0, v___x_5736_);
                lean_ctor_set(v___x_5738_, 1, v___x_5737_);
                v___x_5739_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5739_, 0, v_a_5729_);
                lean_ctor_set(v___x_5739_, 1, v___x_5738_);
                v___x_5740_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_5722_, v___x_5719_, v___x_5723_, v_options_5716_, v___x_5725_, v___y_5727_, v___f_5721_, v___x_5739_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_);
                return v___x_5740_;
            }
            2 => {
                v___x_5745_ = lean_io_get_num_heartbeats();
                v___x_5746_ = lean_float_of_nat(v___y_5743_);
                v___x_5747_ = lean_float_of_nat(v___x_5745_);
                v___x_5748_ = lean_box_float(v___x_5746_);
                v___x_5749_ = lean_box_float(v___x_5747_);
                v___x_5750_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5750_, 0, v___x_5748_);
                lean_ctor_set(v___x_5750_, 1, v___x_5749_);
                v___x_5751_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5751_, 0, v_a_5744_);
                lean_ctor_set(v___x_5751_, 1, v___x_5750_);
                v___x_5752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7(v_cls_5722_, v___x_5719_, v___x_5723_, v_options_5716_, v___x_5725_, v___y_5742_, v___f_5721_, v___x_5751_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_);
                return v___x_5752_;
            }
            3 => {
                v___x_5754_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__5___redArg(v_a_5714_);
                v_a_5755_ = lean_ctor_get(v___x_5754_, 0);
                lean_inc(v_a_5755_);
                lean_dec_ref(v___x_5754_);
                v___x_5756_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_5757_ = l_Lean_Option_get___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__6(v_options_5716_, v___x_5756_);
                if v___x_5757_ == 0 {
                    v___x_5758_ = lean_io_mono_nanos_now();
                    v___x_5759_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_5710_, v_t_5708_, v_s_5709_, v___x_5719_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_);
                    if lean_obj_tag(v___x_5759_) == 0 {
                        v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
                        v_isSharedCheck_5767_ = (!lean_is_exclusive(v___x_5759_)) as u8;
                        if v_isSharedCheck_5767_ == 0 {
                            v___x_5762_ = v___x_5759_;
                            v_isShared_5763_ = v_isSharedCheck_5767_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5760_);
                            lean_dec(v___x_5759_);
                            v___x_5762_ = lean_box(0);
                            v_isShared_5763_ = v_isSharedCheck_5767_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_5768_ = lean_ctor_get(v___x_5759_, 0);
                        v_isSharedCheck_5775_ = (!lean_is_exclusive(v___x_5759_)) as u8;
                        if v_isSharedCheck_5775_ == 0 {
                            v___x_5770_ = v___x_5759_;
                            v_isShared_5771_ = v_isSharedCheck_5775_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5768_);
                            lean_dec(v___x_5759_);
                            v___x_5770_ = lean_box(0);
                            v_isShared_5771_ = v_isSharedCheck_5775_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_5776_ = lean_io_get_num_heartbeats();
                    v___x_5777_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4(v_candidate_5710_, v_t_5708_, v_s_5709_, v___x_5719_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_);
                    if lean_obj_tag(v___x_5777_) == 0 {
                        v_a_5778_ = lean_ctor_get(v___x_5777_, 0);
                        v_isSharedCheck_5785_ = (!lean_is_exclusive(v___x_5777_)) as u8;
                        if v_isSharedCheck_5785_ == 0 {
                            v___x_5780_ = v___x_5777_;
                            v_isShared_5781_ = v_isSharedCheck_5785_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5778_);
                            lean_dec(v___x_5777_);
                            v___x_5780_ = lean_box(0);
                            v_isShared_5781_ = v_isSharedCheck_5785_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_5786_ = lean_ctor_get(v___x_5777_, 0);
                        v_isSharedCheck_5793_ = (!lean_is_exclusive(v___x_5777_)) as u8;
                        if v_isSharedCheck_5793_ == 0 {
                            v___x_5788_ = v___x_5777_;
                            v_isShared_5789_ = v_isSharedCheck_5793_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_5786_);
                            lean_dec(v___x_5777_);
                            v___x_5788_ = lean_box(0);
                            v_isShared_5789_ = v_isSharedCheck_5793_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_5763_ == 0 {
                    lean_ctor_set_tag(v___x_5762_, 1);
                    v___x_5765_ = v___x_5762_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_a_5760_);
                    v___x_5765_ = v_reuseFailAlloc_5766_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5727_ = v_a_5755_;
                v___y_5728_ = v___x_5758_;
                v_a_5729_ = v___x_5765_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_5771_ == 0 {
                    lean_ctor_set_tag(v___x_5770_, 0);
                    v___x_5773_ = v___x_5770_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_a_5768_);
                    v___x_5773_ = v_reuseFailAlloc_5774_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5727_ = v_a_5755_;
                v___y_5728_ = v___x_5758_;
                v_a_5729_ = v___x_5773_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_5781_ == 0 {
                    lean_ctor_set_tag(v___x_5780_, 1);
                    v___x_5783_ = v___x_5780_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
                    v___x_5783_ = v_reuseFailAlloc_5784_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_5742_ = v_a_5755_;
                v___y_5743_ = v___x_5776_;
                v_a_5744_ = v___x_5783_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_5789_ == 0 {
                    lean_ctor_set_tag(v___x_5788_, 0);
                    v___x_5791_ = v___x_5788_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5786_);
                    v___x_5791_ = v_reuseFailAlloc_5792_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_5742_ = v_a_5755_;
                v___y_5743_ = v___x_5776_;
                v_a_5744_ = v___x_5791_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___boxed(
    mut v_t_5797_: *mut LeanObject,
    mut v_s_5798_: *mut LeanObject,
    mut v_candidate_5799_: *mut LeanObject,
    mut v_a_5800_: *mut LeanObject,
    mut v_a_5801_: *mut LeanObject,
    mut v_a_5802_: *mut LeanObject,
    mut v_a_5803_: *mut LeanObject,
    mut v_a_5804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5805_: *mut LeanObject = core::ptr::null_mut();
    v_res_5805_ =
        l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(
            v_t_5797_,
            v_s_5798_,
            v_candidate_5799_,
            v_a_5800_,
            v_a_5801_,
            v_a_5802_,
            v_a_5803_,
        );
    lean_dec(v_a_5803_);
    lean_dec_ref(v_a_5802_);
    lean_dec(v_a_5801_);
    lean_dec_ref(v_a_5800_);
    return v_res_5805_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(
    mut v_as_5806_: *mut LeanObject,
    mut v_as_x27_5807_: *mut LeanObject,
    mut v_b_5808_: *mut LeanObject,
    mut v_a_5809_: *mut LeanObject,
    mut v___y_5810_: *mut LeanObject,
    mut v___y_5811_: *mut LeanObject,
    mut v___y_5812_: *mut LeanObject,
    mut v___y_5813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    v___x_5815_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg(v_as_x27_5807_, v_b_5808_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_);
    return v___x_5815_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___boxed(
    mut v_as_5816_: *mut LeanObject,
    mut v_as_x27_5817_: *mut LeanObject,
    mut v_b_5818_: *mut LeanObject,
    mut v_a_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5825_: *mut LeanObject = core::ptr::null_mut();
    v_res_5825_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1(v_as_5816_, v_as_x27_5817_, v_b_5818_, v_a_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_);
    lean_dec(v___y_5823_);
    lean_dec_ref(v___y_5822_);
    lean_dec(v___y_5821_);
    lean_dec_ref(v___y_5820_);
    lean_dec(v_as_x27_5817_);
    lean_dec(v_as_5816_);
    return v_res_5825_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(
    mut v_00_u03b1_5826_: *mut LeanObject,
    mut v_x_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
    mut v___y_5830_: *mut LeanObject,
    mut v___y_5831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    v___x_5833_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___redArg(v_x_5827_);
    return v___x_5833_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9___boxed(
    mut v_00_u03b1_5834_: *mut LeanObject,
    mut v_x_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v___y_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5841_: *mut LeanObject = core::ptr::null_mut();
    v_res_5841_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__7_spec__9(v_00_u03b1_5834_, v_x_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
    lean_dec(v___y_5839_);
    lean_dec_ref(v___y_5838_);
    lean_dec(v___y_5837_);
    lean_dec_ref(v___y_5836_);
    return v_res_5841_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(
    mut v_t_5842_: *mut LeanObject,
    mut v_s_5843_: *mut LeanObject,
    mut v___x_5844_: u8,
    mut v_as_5845_: *mut LeanObject,
    mut v_sz_5846_: usize,
    mut v_i_5847_: usize,
    mut v_b_5848_: *mut LeanObject,
    mut v___y_5849_: *mut LeanObject,
    mut v___y_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5854_: u8 = 0;
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5861_: u8 = 0;
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: u8 = 0;
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: usize = 0;
    let mut v___x_5866_: usize = 0;
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut v_a_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5878_: u8 = 0;
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5854_ = lean_usize_dec_lt(v_i_5847_, v_sz_5846_);
                if v___x_5854_ == 0 {
                    lean_dec_ref(v_s_5843_);
                    lean_dec_ref(v_t_5842_);
                    v___x_5855_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5855_, 0, v_b_5848_);
                    return v___x_5855_;
                } else {
                    lean_dec_ref(v_b_5848_);
                    v_a_5856_ = lean_array_uget_borrowed(v_as_5845_, v_i_5847_);
                    lean_inc(v_a_5856_);
                    lean_inc_ref(v_s_5843_);
                    lean_inc_ref(v_t_5842_);
                    v___x_5857_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate(v_t_5842_, v_s_5843_, v_a_5856_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_);
                    if lean_obj_tag(v___x_5857_) == 0 {
                        v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
                        v_isSharedCheck_5874_ = (!lean_is_exclusive(v___x_5857_)) as u8;
                        if v_isSharedCheck_5874_ == 0 {
                            v___x_5860_ = v___x_5857_;
                            v_isShared_5861_ = v_isSharedCheck_5874_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5858_);
                            lean_dec(v___x_5857_);
                            v___x_5860_ = lean_box(0);
                            v_isShared_5861_ = v_isSharedCheck_5874_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_s_5843_);
                        lean_dec_ref(v_t_5842_);
                        v_a_5875_ = lean_ctor_get(v___x_5857_, 0);
                        v_isSharedCheck_5882_ = (!lean_is_exclusive(v___x_5857_)) as u8;
                        if v_isSharedCheck_5882_ == 0 {
                            v___x_5877_ = v___x_5857_;
                            v_isShared_5878_ = v_isSharedCheck_5882_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5875_);
                            lean_dec(v___x_5857_);
                            v___x_5877_ = lean_box(0);
                            v_isShared_5878_ = v_isSharedCheck_5882_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5862_ = lean_box(0);
                v___x_5863_ = (lean_unbox(v_a_5858_) as u8);
                lean_dec(v_a_5858_);
                if v___x_5863_ == 0 {
                    lean_del_object(v___x_5860_);
                    v___x_5864_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0;
                    v___x_5865_ = 1usize;
                    v___x_5866_ = lean_usize_add(v_i_5847_, v___x_5865_);
                    v_i_5847_ = v___x_5866_;
                    v_b_5848_ = v___x_5864_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_s_5843_);
                    lean_dec_ref(v_t_5842_);
                    v___x_5868_ = lean_box((v___x_5844_) as usize);
                    v___x_5869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5869_, 0, v___x_5868_);
                    v___x_5870_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5870_, 0, v___x_5869_);
                    lean_ctor_set(v___x_5870_, 1, v___x_5862_);
                    if v_isShared_5861_ == 0 {
                        lean_ctor_set(v___x_5860_, 0, v___x_5870_);
                        v___x_5872_ = v___x_5860_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5873_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5873_, 0, v___x_5870_);
                        v___x_5872_ = v_reuseFailAlloc_5873_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5872_;
            }
            3 => {
                if v_isShared_5878_ == 0 {
                    v___x_5880_ = v___x_5877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5875_);
                    v___x_5880_ = v_reuseFailAlloc_5881_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0___boxed(
    mut v_t_5883_: *mut LeanObject,
    mut v_s_5884_: *mut LeanObject,
    mut v___x_5885_: *mut LeanObject,
    mut v_as_5886_: *mut LeanObject,
    mut v_sz_5887_: *mut LeanObject,
    mut v_i_5888_: *mut LeanObject,
    mut v_b_5889_: *mut LeanObject,
    mut v___y_5890_: *mut LeanObject,
    mut v___y_5891_: *mut LeanObject,
    mut v___y_5892_: *mut LeanObject,
    mut v___y_5893_: *mut LeanObject,
    mut v___y_5894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3586__boxed_5895_: u8 = 0;
    let mut v_sz_boxed_5896_: usize = 0;
    let mut v_i_boxed_5897_: usize = 0;
    let mut v_res_5898_: *mut LeanObject = core::ptr::null_mut();
    v___x_3586__boxed_5895_ = (lean_unbox(v___x_5885_) as u8);
    v_sz_boxed_5896_ = lean_unbox_usize(v_sz_5887_);
    lean_dec(v_sz_5887_);
    v_i_boxed_5897_ = lean_unbox_usize(v_i_5888_);
    lean_dec(v_i_5888_);
    v_res_5898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_5883_, v_s_5884_, v___x_3586__boxed_5895_, v_as_5886_, v_sz_boxed_5896_, v_i_boxed_5897_, v_b_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
    lean_dec(v___y_5893_);
    lean_dec_ref(v___y_5892_);
    lean_dec(v___y_5891_);
    lean_dec_ref(v___y_5890_);
    lean_dec_ref(v_as_5886_);
    return v_res_5898_;
}
pub unsafe fn l_Lean_Meta_tryUnificationHints(
    mut v_t_5899_: *mut LeanObject,
    mut v_s_5900_: *mut LeanObject,
    mut v_a_5901_: *mut LeanObject,
    mut v_a_5902_: *mut LeanObject,
    mut v_a_5903_: *mut LeanObject,
    mut v_a_5904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unificationHints_5912_: u8 = 0;
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: u8 = 0;
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5924_: u8 = 0;
    let mut v_zetaDeltaSet_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5931_: u8 = 0;
    let mut v_inTypeClassResolution_5932_: u8 = 0;
    let mut v_cacheInferType_5933_: u8 = 0;
    let mut v___x_5934_: u64 = 0;
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5942_: usize = 0;
    let mut v___x_5943_: usize = 0;
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5948_: u8 = 0;
    let mut v_fst_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5958_: u8 = 0;
    let mut v_a_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5962_: u8 = 0;
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5966_: u8 = 0;
    let mut v_a_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5970_: u8 = 0;
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5974_: u8 = 0;
    let mut v___x_5975_: u8 = 0;
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5979_: u8 = 0;
    let mut v_inheritedTraceOptions_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: u8 = 0;
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5993_: u8 = 0;
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5978_ = lean_ctor_get(v_a_5903_, 2);
                v_hasTrace_5979_ = lean_ctor_get_uint8(
                    v_options_5978_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5979_ == 0 {
                    v___y_5907_ = v_a_5901_;
                    v___y_5908_ = v_a_5902_;
                    v___y_5909_ = v_a_5903_;
                    v___y_5910_ = v_a_5904_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_5980_ = lean_ctor_get(v_a_5903_, 13);
                    v_cls_5981_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5;
                    v___x_5982_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8_once), _init_l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__8);
                    v___x_5983_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5980_,
                        v_options_5978_,
                        v___x_5982_,
                    );
                    if v___x_5983_ == 0 {
                        v___y_5907_ = v_a_5901_;
                        v___y_5908_ = v_a_5902_;
                        v___y_5909_ = v_a_5903_;
                        v___y_5910_ = v_a_5904_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_t_5899_);
                        v___x_5984_ = l_Lean_MessageData_ofExpr(v_t_5899_);
                        v___x_5985_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5_once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate___lam__0___closed__5);
                        v___x_5986_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5986_, 0, v___x_5984_);
                        lean_ctor_set(v___x_5986_, 1, v___x_5985_);
                        lean_inc_ref(v_s_5900_);
                        v___x_5987_ = l_Lean_MessageData_ofExpr(v_s_5900_);
                        v___x_5988_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5988_, 0, v___x_5986_);
                        lean_ctor_set(v___x_5988_, 1, v___x_5987_);
                        v___x_5989_ = l_Lean_addTrace___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__3(v_cls_5981_, v___x_5988_, v_a_5901_, v_a_5902_, v_a_5903_, v_a_5904_);
                        if lean_obj_tag(v___x_5989_) == 0 {
                            lean_dec_ref_known(v___x_5989_, 1);
                            v___y_5907_ = v_a_5901_;
                            v___y_5908_ = v_a_5902_;
                            v___y_5909_ = v_a_5903_;
                            v___y_5910_ = v_a_5904_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_s_5900_);
                            lean_dec_ref(v_t_5899_);
                            v_a_5990_ = lean_ctor_get(v___x_5989_, 0);
                            v_isSharedCheck_5997_ = (!lean_is_exclusive(v___x_5989_)) as u8;
                            if v_isSharedCheck_5997_ == 0 {
                                v___x_5992_ = v___x_5989_;
                                v_isShared_5993_ = v_isSharedCheck_5997_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_5990_);
                                lean_dec(v___x_5989_);
                                v___x_5992_ = lean_box(0);
                                v_isShared_5993_ = v_isSharedCheck_5997_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5911_ = l_Lean_Meta_Context_config(v___y_5907_);
                v_unificationHints_5912_ = lean_ctor_get_uint8(v___x_5911_, 5 as u32);
                lean_dec_ref(v___x_5911_);
                if v_unificationHints_5912_ == 0 {
                    lean_dec_ref(v_s_5900_);
                    lean_dec_ref(v_t_5899_);
                    v___x_5913_ = lean_box((v_unificationHints_5912_) as usize);
                    v___x_5914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5914_, 0, v___x_5913_);
                    return v___x_5914_;
                } else {
                    v___x_5915_ = l_Lean_Expr_isMVar(v_t_5899_);
                    if v___x_5915_ == 0 {
                        v___x_5916_ = lean_st_ref_get(v___y_5910_);
                        v_env_5917_ = lean_ctor_get(v___x_5916_, 0);
                        lean_inc_ref(v_env_5917_);
                        lean_dec(v___x_5916_);
                        v___x_5918_ = l_Lean_Meta_unificationHintExtension;
                        v_ext_5919_ = lean_ctor_get(v___x_5918_, 1);
                        v_toEnvExtension_5920_ = lean_ctor_get(v_ext_5919_, 0);
                        v_asyncMode_5921_ = lean_ctor_get(v_toEnvExtension_5920_, 2);
                        v___x_5922_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config;
                        v_config_5923_ = lean_ctor_get(v___x_5922_, 0);
                        v_trackZetaDelta_5924_ = lean_ctor_get_uint8(
                            v___y_5907_,
                            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        );
                        v_zetaDeltaSet_5925_ = lean_ctor_get(v___y_5907_, 1);
                        v_lctx_5926_ = lean_ctor_get(v___y_5907_, 2);
                        v_localInstances_5927_ = lean_ctor_get(v___y_5907_, 3);
                        v_defEqCtx_x3f_5928_ = lean_ctor_get(v___y_5907_, 4);
                        v_synthPendingDepth_5929_ = lean_ctor_get(v___y_5907_, 5);
                        v_canUnfold_x3f_5930_ = lean_ctor_get(v___y_5907_, 6);
                        v_univApprox_5931_ = lean_ctor_get_uint8(
                            v___y_5907_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        );
                        v_inTypeClassResolution_5932_ = lean_ctor_get_uint8(
                            v___y_5907_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        );
                        v_cacheInferType_5933_ = lean_ctor_get_uint8(
                            v___y_5907_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        );
                        v___x_5934_ =
                            l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_5923_);
                        v___x_5935_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instInhabitedUnificationHints_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instInhabitedUnificationHints_default___closed__0_once
                            ),
                            _init_l_Lean_Meta_instInhabitedUnificationHints_default___closed__0,
                        );
                        v___x_5936_ = l_Lean_ScopedEnvExtension_getState___redArg(
                            v___x_5935_,
                            v___x_5918_,
                            v_env_5917_,
                            v_asyncMode_5921_,
                        );
                        lean_inc_ref(v_config_5923_);
                        v___x_5937_ = lean_alloc_ctor(0, 1, (8) as u32);
                        lean_ctor_set(v___x_5937_, 0, v_config_5923_);
                        lean_ctor_set_uint64(
                            v___x_5937_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_5934_,
                        );
                        lean_inc(v_canUnfold_x3f_5930_);
                        lean_inc(v_synthPendingDepth_5929_);
                        lean_inc(v_defEqCtx_x3f_5928_);
                        lean_inc_ref(v_localInstances_5927_);
                        lean_inc_ref(v_lctx_5926_);
                        lean_inc(v_zetaDeltaSet_5925_);
                        v___x_5938_ = lean_alloc_ctor(0, 7, (4) as u32);
                        lean_ctor_set(v___x_5938_, 0, v___x_5937_);
                        lean_ctor_set(v___x_5938_, 1, v_zetaDeltaSet_5925_);
                        lean_ctor_set(v___x_5938_, 2, v_lctx_5926_);
                        lean_ctor_set(v___x_5938_, 3, v_localInstances_5927_);
                        lean_ctor_set(v___x_5938_, 4, v_defEqCtx_x3f_5928_);
                        lean_ctor_set(v___x_5938_, 5, v_synthPendingDepth_5929_);
                        lean_ctor_set(v___x_5938_, 6, v_canUnfold_x3f_5930_);
                        lean_ctor_set_uint8(
                            v___x_5938_,
                            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                            v_trackZetaDelta_5924_,
                        );
                        lean_ctor_set_uint8(
                            v___x_5938_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                            v_univApprox_5931_,
                        );
                        lean_ctor_set_uint8(
                            v___x_5938_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                            v_inTypeClassResolution_5932_,
                        );
                        lean_ctor_set_uint8(
                            v___x_5938_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                            v_cacheInferType_5933_,
                        );
                        lean_inc_ref(v_t_5899_);
                        v___x_5939_ = l_Lean_Meta_DiscrTree_getMatch___redArg(
                            v___x_5936_,
                            v_t_5899_,
                            v___x_5938_,
                            v___y_5908_,
                            v___y_5909_,
                            v___y_5910_,
                        );
                        lean_dec_ref_known(v___x_5938_, 7);
                        lean_dec(v___x_5936_);
                        if lean_obj_tag(v___x_5939_) == 0 {
                            v_a_5940_ = lean_ctor_get(v___x_5939_, 0);
                            lean_inc(v_a_5940_);
                            lean_dec_ref_known(v___x_5939_, 1);
                            v___x_5941_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__1___redArg___closed__0;
                            v_sz_5942_ = lean_array_size(v_a_5940_);
                            v___x_5943_ = 0usize;
                            v___x_5944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_tryUnificationHints_spec__0(v_t_5899_, v_s_5900_, v_unificationHints_5912_, v_a_5940_, v_sz_5942_, v___x_5943_, v___x_5941_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
                            lean_dec(v_a_5940_);
                            if lean_obj_tag(v___x_5944_) == 0 {
                                v_a_5945_ = lean_ctor_get(v___x_5944_, 0);
                                v_isSharedCheck_5958_ = (!lean_is_exclusive(v___x_5944_)) as u8;
                                if v_isSharedCheck_5958_ == 0 {
                                    v___x_5947_ = v___x_5944_;
                                    v_isShared_5948_ = v_isSharedCheck_5958_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_5945_);
                                    lean_dec(v___x_5944_);
                                    v___x_5947_ = lean_box(0);
                                    v_isShared_5948_ = v_isSharedCheck_5958_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_5959_ = lean_ctor_get(v___x_5944_, 0);
                                v_isSharedCheck_5966_ = (!lean_is_exclusive(v___x_5944_)) as u8;
                                if v_isSharedCheck_5966_ == 0 {
                                    v___x_5961_ = v___x_5944_;
                                    v_isShared_5962_ = v_isSharedCheck_5966_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5959_);
                                    lean_dec(v___x_5944_);
                                    v___x_5961_ = lean_box(0);
                                    v_isShared_5962_ = v_isSharedCheck_5966_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_s_5900_);
                            lean_dec_ref(v_t_5899_);
                            v_a_5967_ = lean_ctor_get(v___x_5939_, 0);
                            v_isSharedCheck_5974_ = (!lean_is_exclusive(v___x_5939_)) as u8;
                            if v_isSharedCheck_5974_ == 0 {
                                v___x_5969_ = v___x_5939_;
                                v_isShared_5970_ = v_isSharedCheck_5974_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_5967_);
                                lean_dec(v___x_5939_);
                                v___x_5969_ = lean_box(0);
                                v_isShared_5970_ = v_isSharedCheck_5974_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_s_5900_);
                        lean_dec_ref(v_t_5899_);
                        v___x_5975_ = 0;
                        v___x_5976_ = lean_box((v___x_5975_) as usize);
                        v___x_5977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5977_, 0, v___x_5976_);
                        return v___x_5977_;
                    }
                }
            }
            2 => {
                v_fst_5949_ = lean_ctor_get(v_a_5945_, 0);
                lean_inc(v_fst_5949_);
                lean_dec(v_a_5945_);
                if lean_obj_tag(v_fst_5949_) == 0 {
                    v___x_5950_ = lean_box((v___x_5915_) as usize);
                    if v_isShared_5948_ == 0 {
                        lean_ctor_set(v___x_5947_, 0, v___x_5950_);
                        v___x_5952_ = v___x_5947_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5950_);
                        v___x_5952_ = v_reuseFailAlloc_5953_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_5954_ = lean_ctor_get(v_fst_5949_, 0);
                    lean_inc(v_val_5954_);
                    lean_dec_ref_known(v_fst_5949_, 1);
                    if v_isShared_5948_ == 0 {
                        lean_ctor_set(v___x_5947_, 0, v_val_5954_);
                        v___x_5956_ = v___x_5947_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_val_5954_);
                        v___x_5956_ = v_reuseFailAlloc_5957_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5952_;
            }
            4 => {
                return v___x_5956_;
            }
            5 => {
                if v_isShared_5962_ == 0 {
                    v___x_5964_ = v___x_5961_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_a_5959_);
                    v___x_5964_ = v_reuseFailAlloc_5965_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5964_;
            }
            7 => {
                if v_isShared_5970_ == 0 {
                    v___x_5972_ = v___x_5969_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_a_5967_);
                    v___x_5972_ = v_reuseFailAlloc_5973_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5972_;
            }
            9 => {
                if v_isShared_5993_ == 0 {
                    v___x_5995_ = v___x_5992_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_a_5990_);
                    v___x_5995_ = v_reuseFailAlloc_5996_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_tryUnificationHints___boxed(
    mut v_t_5998_: *mut LeanObject,
    mut v_s_5999_: *mut LeanObject,
    mut v_a_6000_: *mut LeanObject,
    mut v_a_6001_: *mut LeanObject,
    mut v_a_6002_: *mut LeanObject,
    mut v_a_6003_: *mut LeanObject,
    mut v_a_6004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6005_: *mut LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_Lean_Meta_tryUnificationHints(
        v_t_5998_, v_s_5999_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_,
    );
    lean_dec(v_a_6003_);
    lean_dec_ref(v_a_6002_);
    lean_dec(v_a_6001_);
    lean_dec_ref(v_a_6000_);
    return v_res_6005_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    v___x_6006_ = lean_unsigned_to_nat(2674080740);
    v___x_6007_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_6008_ = l_Lean_Name_num___override(v___x_6007_, v___x_6006_);
    return v___x_6008_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    v___x_6009_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_6010_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
    v___x_6011_ = l_Lean_Name_str___override(v___x_6010_, v___x_6009_);
    return v___x_6011_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    v___x_6012_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_;
    v___x_6013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
    v___x_6014_ = l_Lean_Name_str___override(v___x_6013_, v___x_6012_);
    return v___x_6014_;
}
pub unsafe fn _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    v___x_6015_ = lean_unsigned_to_nat(2);
    v___x_6016_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
    v___x_6017_ = l_Lean_Name_num___override(v___x_6016_, v___x_6015_);
    return v___x_6017_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: u8 = 0;
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    v___x_6019_ = l_Lean_Meta_checkpointDefEq___at___00__private_Lean_Meta_UnificationHint_0__Lean_Meta_tryUnificationHints_tryCandidate_spec__4___closed__5;
    v___x_6020_ = 0;
    v___x_6021_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_);
    v___x_6022_ = l_Lean_registerTraceClass(v___x_6019_, v___x_6020_, v___x_6021_);
    return v___x_6022_;
}
pub unsafe fn l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2____boxed(
    mut v_a_6023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6024_: *mut LeanObject = core::ptr::null_mut();
    v_res_6024_ = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
    return v_res_6024_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_UnificationHint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_instInhabitedUnificationHints_default =
        _init_l_Lean_Meta_instInhabitedUnificationHints_default();
    lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints_default);
    l_Lean_Meta_instInhabitedUnificationHints = _init_l_Lean_Meta_instInhabitedUnificationHints();
    lean_mark_persistent(l_Lean_Meta_instInhabitedUnificationHints);
    l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config =
        _init_l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config();
    lean_mark_persistent(l___private_Lean_Meta_UnificationHint_0__Lean_Meta_config);
    res = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_1858784148____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_unificationHintExtension = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_unificationHintExtension);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_3033092106____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_UnificationHint_0__Lean_Meta_initFn_00___x40_Lean_Meta_UnificationHint_2674080740____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_UnificationHint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_UnificationHint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_UnificationHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_UnificationHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_UnificationHint(builtin);
}
