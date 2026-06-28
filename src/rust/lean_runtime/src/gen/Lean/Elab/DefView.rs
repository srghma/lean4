// Lean compiler output
// Module: Lean.Elab.DefView
// Imports: Lean.Elab.DeclNameGen Lean.Elab.DeclUtil
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getSepArgs, l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit, l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node4,
    l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Attributes::l_Lean_Elab_toAttributeKind___boxed;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_getCurrMacroScope___redArg, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg,
};
use crate::r#gen::Lean::Elab::DeclModifiers::{
    l_Lean_Elab_Modifiers_addAttr, l_Lean_Elab_Modifiers_addFirstAttr,
    l_Lean_Elab_Modifiers_filterAttrs, l_Lean_Elab_instBEqComputeKind_beq,
    l_Lean_Elab_instInhabitedModifiers_default,
};
use crate::r#gen::Lean::Elab::DeclNameGen::{
    initialize_Lean_Elab_DeclNameGen, l_Lean_Elab_Command_mkInstanceName,
    runtime_initialize_Lean_Elab_DeclNameGen,
};
use crate::r#gen::Lean::Elab::DeclUtil::{
    initialize_Lean_Elab_DeclUtil, l_Lean_Elab_expandDeclSig, l_Lean_Elab_expandOptDeclSig,
    runtime_initialize_Lean_Elab_DeclUtil,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go;
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_expandMacroImpl_x3f, l_Lean_Elab_expandOptNamedPrio___boxed,
    l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::Language::Basic::{
    l_Lean_Language_SnapshotTask_map___redArg, l_Lean_Language_instInhabitedSnapshotTree_default,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
    l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Lean_Elab_instInhabitedDefKind_default: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedDefKind: u8 = 0;
pub static l_Lean_Elab_instBEqDefKind___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instBEqDefKind_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instBEqDefKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqDefKind___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Elab_instBEqDefKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqDefKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value:
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
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value:
    LeanStringObject<20> = LeanStringObject {
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
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0_value:
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
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [68, 101, 102, 115, 80, 97, 114, 115, 101, 100, 83, 110, 97, 112, 115, 104, 111, 116, 0]};
static mut l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject;
static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,4408595883411259083 as *mut LeanObject] };
static mut l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject;
pub static mut l_Lean_Elab_instImpl_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject;
pub static mut l_Lean_Elab_instTypeNameDefsParsedSnapshot: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_instInhabitedDefView_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedDefView_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefView_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefView: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut LeanObject,5908072408641034476 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value: LeanStringObject<6> =
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
        m_data: [100, 101, 102, 101, 113, 0],
    };
static mut l_Lean_Elab_DefView_markDefEq___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value)
                as *mut LeanObject,
            4826972851695508558 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_DefView_markDefEq___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_DefView_markDefEq___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_DefView_markDefEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_DefView_markDefEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value: LeanStringObject<7> =
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
        m_data: [105, 110, 108, 105, 110, 101, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value)
                as *mut LeanObject,
            8159932143332935260 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value: LeanStringObject<10> =
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
        m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value)
                as *mut LeanObject,
            7045040058828669725 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2_value
) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0_value: LeanStringObject<158> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value: LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value: LeanStringObject<7> =
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
        m_data: [100, 101, 99, 108, 73, 100, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value: LeanStringObject<5> =
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
        m_data: [65, 116, 116, 114, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value)
                as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut LeanObject,12927425362287788416 as *mut LeanObject] };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value: LeanStringObject<15> =
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
            109, 107, 73, 110, 115, 116, 97, 110, 99, 101, 78, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut LeanObject,3223284126629939794 as *mut LeanObject] };
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value)
                as *mut LeanObject,
            15410416404573358003 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_value: LeanStringObject<11> =
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
        m_data: [103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_value: LeanStringObject<6> =
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
        m_data: [32, 102, 111, 114, 32, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value: LeanStringObject<14> =
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
            100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value)
                as *mut LeanObject,
            13585030837571646948 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2_value: LeanStringObject<3> =
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
        m_data: [58, 61, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value: LeanStringObject<12> =
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
        m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value: LeanStringObject<7> =
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
        m_data: [115, 117, 102, 102, 105, 120, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value)
                as *mut LeanObject,
            7625897890118033792 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value)
                as *mut LeanObject,
            8715860392475343861 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value) as *mut LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value: LeanStringObject<20> =
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
            100, 101, 102, 97, 117, 108, 116, 79, 114, 79, 102, 78, 111, 110, 101, 109, 112, 116,
            121, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value) as *mut LeanObject;
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value)
                as *mut LeanObject,
            14701813571789919052 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10_value: LeanStringObject<23> =
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
            100, 101, 102, 97, 117, 108, 116, 95, 111, 114, 95, 111, 102, 78, 111, 110, 101, 109,
            112, 116, 121, 37, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11_value: LeanStringObject<7> =
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
        m_data: [117, 110, 115, 97, 102, 101, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value: LeanStringObject<9> =
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
        m_data: [95, 101, 120, 97, 109, 112, 108, 101, 0],
    };
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value)
                as *mut LeanObject,
            8858487489706526963 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value)
                as *mut LeanObject,
            1827444229220621555 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__0_value: LeanStringObject<8> =
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
        m_data: [116, 104, 101, 111, 114, 101, 109, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_isDefLike___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__0_value) as *mut LeanObject,
        3907549710869165294 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_isDefLike___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__2_value: LeanStringObject<7> =
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
        m_data: [111, 112, 97, 113, 117, 101, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_isDefLike___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__2_value) as *mut LeanObject,
        7407402195942431087 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_isDefLike___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_isDefLike___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut LeanObject,11064845058293668901 as *mut LeanObject] };
static mut l_Lean_Elab_Command_isDefLike___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__5_value: LeanStringObject<8> =
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
        m_data: [101, 120, 97, 109, 112, 108, 101, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__5_value) as *mut LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_isDefLike___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__5_value) as *mut LeanObject,
        16587644253004373100 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_isDefLike___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__7_value: LeanStringObject<7> =
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
        m_data: [97, 98, 98, 114, 101, 118, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__7_value) as *mut LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_isDefLike___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__7_value) as *mut LeanObject,
        7158170725601883426 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_isDefLike___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__9_value: LeanStringObject<11> =
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
        m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__9_value) as *mut LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Command_isDefLike___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_isDefLike___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__9_value) as *mut LeanObject,
        9789339221525904376 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_isDefLike___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_mkDefView___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 107, 105, 110, 100, 32, 111, 102,
            32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkDefView___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefView___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Command_mkDefView___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_mkDefView___closed__1: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__9_value) as *mut LeanObject,6897119537390546559 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [68, 101, 102, 86, 105, 101, 119, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,530979614227987087 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,16822043437053200418 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,14199109792594499331 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,12046185499159403317 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value) as *mut LeanObject,7427837794232889372 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,3339763488256995113 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,7838269638771429444 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,15708863969511340069 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut LeanObject,9051532757897805587 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,17829560872556345656 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,((( 1745620379 as usize) << 1) | 1) as *mut LeanObject,5347715228956474749 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,507745096295086142 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,7792782298071999666 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,3010035636668721035 as *mut LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_DefKind_ctorIdx(mut v_x_2285_: u8) -> *mut LeanObject {
    match v_x_2285_ {
        0 => {
            let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
            v___x_2286_ = lean_unsigned_to_nat(0);
            return v___x_2286_;
        }
        1 => {
            let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
            v___x_2287_ = lean_unsigned_to_nat(1);
            return v___x_2287_;
        }
        2 => {
            let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
            v___x_2288_ = lean_unsigned_to_nat(2);
            return v___x_2288_;
        }
        3 => {
            let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
            v___x_2289_ = lean_unsigned_to_nat(3);
            return v___x_2289_;
        }
        4 => {
            let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
            v___x_2290_ = lean_unsigned_to_nat(4);
            return v___x_2290_;
        }
        _ => {
            let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
            v___x_2291_ = lean_unsigned_to_nat(5);
            return v___x_2291_;
        }
    }
}
pub unsafe fn l_Lean_Elab_DefKind_ctorIdx___boxed(
    mut v_x_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2293_: u8 = 0;
    let mut v_res_2294_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2293_ = (lean_unbox(v_x_2292_) as u8);
    v_res_2294_ = l_Lean_Elab_DefKind_ctorIdx(v_x_boxed_2293_);
    return v_res_2294_;
}
pub unsafe fn l_Lean_Elab_DefKind_toCtorIdx(mut v_x_2295_: u8) -> *mut LeanObject {
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    v___x_2296_ = l_Lean_Elab_DefKind_ctorIdx(v_x_2295_);
    return v___x_2296_;
}
pub unsafe fn l_Lean_Elab_DefKind_toCtorIdx___boxed(
    mut v_x_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_2298_: u8 = 0;
    let mut v_res_2299_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2298_ = (lean_unbox(v_x_2297_) as u8);
    v_res_2299_ = l_Lean_Elab_DefKind_toCtorIdx(v_x_4__boxed_2298_);
    return v_res_2299_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim___redArg(
    mut v_k_2300_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2300_);
    return v_k_2300_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim___redArg___boxed(
    mut v_k_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2302_: *mut LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Elab_DefKind_ctorElim___redArg(v_k_2301_);
    lean_dec(v_k_2301_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim(
    mut v_motive_2303_: *mut LeanObject,
    mut v_ctorIdx_2304_: *mut LeanObject,
    mut v_t_2305_: u8,
    mut v_h_2306_: *mut LeanObject,
    mut v_k_2307_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2307_);
    return v_k_2307_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim___boxed(
    mut v_motive_2308_: *mut LeanObject,
    mut v_ctorIdx_2309_: *mut LeanObject,
    mut v_t_2310_: *mut LeanObject,
    mut v_h_2311_: *mut LeanObject,
    mut v_k_2312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2313_: u8 = 0;
    let mut v_res_2314_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2313_ = (lean_unbox(v_t_2310_) as u8);
    v_res_2314_ = l_Lean_Elab_DefKind_ctorElim(
        v_motive_2308_,
        v_ctorIdx_2309_,
        v_t_boxed_2313_,
        v_h_2311_,
        v_k_2312_,
    );
    lean_dec(v_k_2312_);
    lean_dec(v_ctorIdx_2309_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim___redArg(
    mut v_def_2315_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_def_2315_);
    return v_def_2315_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim___redArg___boxed(
    mut v_def_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2317_: *mut LeanObject = core::ptr::null_mut();
    v_res_2317_ = l_Lean_Elab_DefKind_def_elim___redArg(v_def_2316_);
    lean_dec(v_def_2316_);
    return v_res_2317_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim(
    mut v_motive_2318_: *mut LeanObject,
    mut v_t_2319_: u8,
    mut v_h_2320_: *mut LeanObject,
    mut v_def_2321_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_def_2321_);
    return v_def_2321_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim___boxed(
    mut v_motive_2322_: *mut LeanObject,
    mut v_t_2323_: *mut LeanObject,
    mut v_h_2324_: *mut LeanObject,
    mut v_def_2325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2326_: u8 = 0;
    let mut v_res_2327_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2326_ = (lean_unbox(v_t_2323_) as u8);
    v_res_2327_ =
        l_Lean_Elab_DefKind_def_elim(v_motive_2322_, v_t_boxed_2326_, v_h_2324_, v_def_2325_);
    lean_dec(v_def_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim___redArg(
    mut v_instance_2328_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_instance_2328_);
    return v_instance_2328_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim___redArg___boxed(
    mut v_instance_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2330_: *mut LeanObject = core::ptr::null_mut();
    v_res_2330_ = l_Lean_Elab_DefKind_instance_elim___redArg(v_instance_2329_);
    lean_dec(v_instance_2329_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim(
    mut v_motive_2331_: *mut LeanObject,
    mut v_t_2332_: u8,
    mut v_h_2333_: *mut LeanObject,
    mut v_instance_2334_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_instance_2334_);
    return v_instance_2334_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim___boxed(
    mut v_motive_2335_: *mut LeanObject,
    mut v_t_2336_: *mut LeanObject,
    mut v_h_2337_: *mut LeanObject,
    mut v_instance_2338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2339_: u8 = 0;
    let mut v_res_2340_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2339_ = (lean_unbox(v_t_2336_) as u8);
    v_res_2340_ = l_Lean_Elab_DefKind_instance_elim(
        v_motive_2335_,
        v_t_boxed_2339_,
        v_h_2337_,
        v_instance_2338_,
    );
    lean_dec(v_instance_2338_);
    return v_res_2340_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim___redArg(
    mut v_theorem_2341_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_theorem_2341_);
    return v_theorem_2341_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim___redArg___boxed(
    mut v_theorem_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2343_: *mut LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Lean_Elab_DefKind_theorem_elim___redArg(v_theorem_2342_);
    lean_dec(v_theorem_2342_);
    return v_res_2343_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim(
    mut v_motive_2344_: *mut LeanObject,
    mut v_t_2345_: u8,
    mut v_h_2346_: *mut LeanObject,
    mut v_theorem_2347_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_theorem_2347_);
    return v_theorem_2347_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim___boxed(
    mut v_motive_2348_: *mut LeanObject,
    mut v_t_2349_: *mut LeanObject,
    mut v_h_2350_: *mut LeanObject,
    mut v_theorem_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2352_: u8 = 0;
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2352_ = (lean_unbox(v_t_2349_) as u8);
    v_res_2353_ = l_Lean_Elab_DefKind_theorem_elim(
        v_motive_2348_,
        v_t_boxed_2352_,
        v_h_2350_,
        v_theorem_2351_,
    );
    lean_dec(v_theorem_2351_);
    return v_res_2353_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim___redArg(
    mut v_example_2354_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_example_2354_);
    return v_example_2354_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim___redArg___boxed(
    mut v_example_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2356_: *mut LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_Lean_Elab_DefKind_example_elim___redArg(v_example_2355_);
    lean_dec(v_example_2355_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim(
    mut v_motive_2357_: *mut LeanObject,
    mut v_t_2358_: u8,
    mut v_h_2359_: *mut LeanObject,
    mut v_example_2360_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_example_2360_);
    return v_example_2360_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim___boxed(
    mut v_motive_2361_: *mut LeanObject,
    mut v_t_2362_: *mut LeanObject,
    mut v_h_2363_: *mut LeanObject,
    mut v_example_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2365_: u8 = 0;
    let mut v_res_2366_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2365_ = (lean_unbox(v_t_2362_) as u8);
    v_res_2366_ = l_Lean_Elab_DefKind_example_elim(
        v_motive_2361_,
        v_t_boxed_2365_,
        v_h_2363_,
        v_example_2364_,
    );
    lean_dec(v_example_2364_);
    return v_res_2366_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim___redArg(
    mut v_opaque_2367_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_opaque_2367_);
    return v_opaque_2367_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim___redArg___boxed(
    mut v_opaque_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2369_: *mut LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Lean_Elab_DefKind_opaque_elim___redArg(v_opaque_2368_);
    lean_dec(v_opaque_2368_);
    return v_res_2369_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim(
    mut v_motive_2370_: *mut LeanObject,
    mut v_t_2371_: u8,
    mut v_h_2372_: *mut LeanObject,
    mut v_opaque_2373_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_opaque_2373_);
    return v_opaque_2373_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim___boxed(
    mut v_motive_2374_: *mut LeanObject,
    mut v_t_2375_: *mut LeanObject,
    mut v_h_2376_: *mut LeanObject,
    mut v_opaque_2377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2378_: u8 = 0;
    let mut v_res_2379_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2378_ = (lean_unbox(v_t_2375_) as u8);
    v_res_2379_ =
        l_Lean_Elab_DefKind_opaque_elim(v_motive_2374_, v_t_boxed_2378_, v_h_2376_, v_opaque_2377_);
    lean_dec(v_opaque_2377_);
    return v_res_2379_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim___redArg(
    mut v_abbrev_2380_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_abbrev_2380_);
    return v_abbrev_2380_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim___redArg___boxed(
    mut v_abbrev_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2382_: *mut LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Lean_Elab_DefKind_abbrev_elim___redArg(v_abbrev_2381_);
    lean_dec(v_abbrev_2381_);
    return v_res_2382_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim(
    mut v_motive_2383_: *mut LeanObject,
    mut v_t_2384_: u8,
    mut v_h_2385_: *mut LeanObject,
    mut v_abbrev_2386_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_abbrev_2386_);
    return v_abbrev_2386_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim___boxed(
    mut v_motive_2387_: *mut LeanObject,
    mut v_t_2388_: *mut LeanObject,
    mut v_h_2389_: *mut LeanObject,
    mut v_abbrev_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2391_: u8 = 0;
    let mut v_res_2392_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2391_ = (lean_unbox(v_t_2388_) as u8);
    v_res_2392_ =
        l_Lean_Elab_DefKind_abbrev_elim(v_motive_2387_, v_t_boxed_2391_, v_h_2389_, v_abbrev_2390_);
    lean_dec(v_abbrev_2390_);
    return v_res_2392_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefKind_default() -> u8 {
    let mut v___x_2393_: u8 = 0;
    v___x_2393_ = 0;
    return v___x_2393_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefKind() -> u8 {
    let mut v___x_2394_: u8 = 0;
    v___x_2394_ = 0;
    return v___x_2394_;
}
pub unsafe fn l_Lean_Elab_instBEqDefKind_beq(mut v_x_2395_: u8, mut v_y_2396_: u8) -> u8 {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    v___x_2397_ = l_Lean_Elab_DefKind_ctorIdx(v_x_2395_);
    v___x_2398_ = l_Lean_Elab_DefKind_ctorIdx(v_y_2396_);
    v___x_2399_ = lean_nat_dec_eq(v___x_2397_, v___x_2398_);
    lean_dec(v___x_2398_);
    lean_dec(v___x_2397_);
    return v___x_2399_;
}
pub unsafe fn l_Lean_Elab_instBEqDefKind_beq___boxed(
    mut v_x_2400_: *mut LeanObject,
    mut v_y_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_2402_: u8 = 0;
    let mut v_y_18__boxed_2403_: u8 = 0;
    let mut v_res_2404_: u8 = 0;
    let mut v_r_2405_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2402_ = (lean_unbox(v_x_2400_) as u8);
    v_y_18__boxed_2403_ = (lean_unbox(v_y_2401_) as u8);
    v_res_2404_ = l_Lean_Elab_instBEqDefKind_beq(v_x_17__boxed_2402_, v_y_18__boxed_2403_);
    v_r_2405_ = lean_box((v_res_2404_) as usize);
    return v_r_2405_;
}
pub unsafe fn l_Lean_Elab_DefKind_isTheorem(mut v_x_2408_: u8) -> u8 {
    if v_x_2408_ == 2 {
        let mut v___x_2409_: u8 = 0;
        v___x_2409_ = 1;
        return v___x_2409_;
    } else {
        let mut v___x_2410_: u8 = 0;
        v___x_2410_ = 0;
        return v___x_2410_;
    }
}
pub unsafe fn l_Lean_Elab_DefKind_isTheorem___boxed(
    mut v_x_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_21__boxed_2412_: u8 = 0;
    let mut v_res_2413_: u8 = 0;
    let mut v_r_2414_: *mut LeanObject = core::ptr::null_mut();
    v_x_21__boxed_2412_ = (lean_unbox(v_x_2411_) as u8);
    v_res_2413_ = l_Lean_Elab_DefKind_isTheorem(v_x_21__boxed_2412_);
    v_r_2414_ = lean_box((v_res_2413_) as usize);
    return v_r_2414_;
}
pub unsafe fn l_Lean_Elab_DefKind_isExample(mut v_x_2415_: u8) -> u8 {
    if v_x_2415_ == 3 {
        let mut v___x_2416_: u8 = 0;
        v___x_2416_ = 1;
        return v___x_2416_;
    } else {
        let mut v___x_2417_: u8 = 0;
        v___x_2417_ = 0;
        return v___x_2417_;
    }
}
pub unsafe fn l_Lean_Elab_DefKind_isExample___boxed(
    mut v_x_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_21__boxed_2419_: u8 = 0;
    let mut v_res_2420_: u8 = 0;
    let mut v_r_2421_: *mut LeanObject = core::ptr::null_mut();
    v_x_21__boxed_2419_ = (lean_unbox(v_x_2418_) as u8);
    v_res_2420_ = l_Lean_Elab_DefKind_isExample(v_x_21__boxed_2419_);
    v_r_2421_ = lean_box((v_res_2420_) as usize);
    return v_r_2421_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3()
-> *mut LeanObject {
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    v___x_2427_ = lean_box(0);
    v___x_2428_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2;
    v___x_2429_ = l_Lean_Expr_const___override(v___x_2428_, v___x_2427_);
    return v___x_2429_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4()
-> *mut LeanObject {
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    v___x_2430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once
        ),
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3,
    );
    v___x_2431_ = lean_unsigned_to_nat(0);
    v___x_2432_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0;
    v___x_2433_ = lean_box(0);
    v___x_2434_ = lean_box(0);
    v___x_2435_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2435_, 0, v___x_2434_);
    lean_ctor_set(v___x_2435_, 1, v___x_2434_);
    lean_ctor_set(v___x_2435_, 2, v___x_2433_);
    lean_ctor_set(v___x_2435_, 3, v___x_2432_);
    lean_ctor_set(v___x_2435_, 4, v___x_2431_);
    lean_ctor_set(v___x_2435_, 5, v___x_2430_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default() -> *mut LeanObject {
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    v___x_2436_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once
        ),
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4,
    );
    return v___x_2436_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData() -> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default;
    return v___x_2437_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(
    mut v_s_2438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSnapshot_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreSnaps_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    v_toSnapshot_2439_ = lean_ctor_get(v_s_2438_, 0);
    v_moreSnaps_2440_ = lean_ctor_get(v_s_2438_, 3);
    lean_inc_ref(v_moreSnaps_2440_);
    lean_inc_ref(v_toSnapshot_2439_);
    v___x_2441_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2441_, 0, v_toSnapshot_2439_);
    lean_ctor_set(v___x_2441_, 1, v_moreSnaps_2440_);
    return v___x_2441_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(
    mut v_s_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2443_: *mut LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(v_s_2442_);
    lean_dec_ref(v_s_2442_);
    return v_res_2443_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(
    mut v_x_2446_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2446_) == 0 {
        let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
        v___x_2447_ = l_Lean_Language_instInhabitedSnapshotTree_default;
        return v___x_2447_;
    } else {
        let mut v_val_2448_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toSnapshot_2449_: *mut LeanObject = core::ptr::null_mut();
        let mut v_moreSnaps_2450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
        v_val_2448_ = lean_ctor_get(v_x_2446_, 0);
        v_toSnapshot_2449_ = lean_ctor_get(v_val_2448_, 0);
        v_moreSnaps_2450_ = lean_ctor_get(v_val_2448_, 3);
        lean_inc_ref(v_moreSnaps_2450_);
        lean_inc_ref(v_toSnapshot_2449_);
        v___x_2451_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2451_, 0, v_toSnapshot_2449_);
        lean_ctor_set(v___x_2451_, 1, v_moreSnaps_2450_);
        return v___x_2451_;
    }
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(
    mut v_x_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2453_: *mut LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v_x_2452_);
    lean_dec(v_x_2452_);
    return v_res_2453_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(
    mut v___f_2457_: *mut LeanObject,
    mut v_s_2458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSnapshot_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bodySnap_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreSnaps_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: u8 = 0;
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: u8 = 0;
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_2459_ = lean_ctor_get(v_s_2458_, 0);
                lean_inc_ref(v_toSnapshot_2459_);
                v_tacSnap_x3f_2460_ = lean_ctor_get(v_s_2458_, 4);
                lean_inc(v_tacSnap_x3f_2460_);
                v_bodySnap_2461_ = lean_ctor_get(v_s_2458_, 6);
                lean_inc_ref(v_bodySnap_2461_);
                v_moreSnaps_2462_ = lean_ctor_get(v_s_2458_, 7);
                lean_inc_ref(v_moreSnaps_2462_);
                lean_dec_ref(v_s_2458_);
                if lean_obj_tag(v_tacSnap_x3f_2460_) == 0 {
                    v___x_2475_ =
                        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0;
                    v___y_2464_ = v___x_2475_;
                    state = 1;
                    continue;
                } else {
                    v_val_2476_ = lean_ctor_get(v_tacSnap_x3f_2460_, 0);
                    lean_inc(v_val_2476_);
                    lean_dec_ref_known(v_tacSnap_x3f_2460_, 1);
                    v_stx_x3f_2477_ = lean_ctor_get(v_val_2476_, 0);
                    lean_inc(v_stx_x3f_2477_);
                    v_reportingRange_2478_ = lean_ctor_get(v_val_2476_, 1);
                    lean_inc(v_reportingRange_2478_);
                    v___x_2479_ =
                        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1;
                    v___x_2480_ = 1;
                    v___x_2481_ = l_Lean_Language_SnapshotTask_map___redArg(
                        v_val_2476_,
                        v___x_2479_,
                        v_stx_x3f_2477_,
                        v_reportingRange_2478_,
                        v___x_2480_,
                    );
                    v___x_2482_ = lean_unsigned_to_nat(1);
                    v___x_2483_ = lean_mk_empty_array_with_capacity(v___x_2482_);
                    v___x_2484_ = lean_array_push(v___x_2483_, v___x_2481_);
                    v___y_2464_ = v___x_2484_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_stx_x3f_2465_ = lean_ctor_get(v_bodySnap_2461_, 0);
                lean_inc(v_stx_x3f_2465_);
                v_reportingRange_2466_ = lean_ctor_get(v_bodySnap_2461_, 1);
                lean_inc(v_reportingRange_2466_);
                v___x_2467_ = 1;
                v___x_2468_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_bodySnap_2461_,
                    v___f_2457_,
                    v_stx_x3f_2465_,
                    v_reportingRange_2466_,
                    v___x_2467_,
                );
                v___x_2469_ = lean_unsigned_to_nat(1);
                v___x_2470_ = lean_mk_empty_array_with_capacity(v___x_2469_);
                v___x_2471_ = lean_array_push(v___x_2470_, v___x_2468_);
                v___x_2472_ = l_Array_append___redArg(v___y_2464_, v___x_2471_);
                lean_dec_ref(v___x_2471_);
                v___x_2473_ = l_Array_append___redArg(v___x_2472_, v_moreSnaps_2462_);
                lean_dec_ref(v_moreSnaps_2462_);
                v___x_2474_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2474_, 0, v_toSnapshot_2459_);
                lean_ctor_set(v___x_2474_, 1, v___x_2473_);
                return v___x_2474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(
    mut v___f_2498_: *mut LeanObject,
    mut v_x_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bodySnap_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreSnaps_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: u8 = 0;
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2499_) == 0 {
                    lean_dec_ref(v___f_2498_);
                    v___x_2500_ = l_Lean_Language_instInhabitedSnapshotTree_default;
                    return v___x_2500_;
                } else {
                    v_val_2501_ = lean_ctor_get(v_x_2499_, 0);
                    lean_inc(v_val_2501_);
                    lean_dec_ref_known(v_x_2499_, 1);
                    v_toSnapshot_2502_ = lean_ctor_get(v_val_2501_, 0);
                    lean_inc_ref(v_toSnapshot_2502_);
                    v_tacSnap_x3f_2503_ = lean_ctor_get(v_val_2501_, 4);
                    lean_inc(v_tacSnap_x3f_2503_);
                    v_bodySnap_2504_ = lean_ctor_get(v_val_2501_, 6);
                    lean_inc_ref(v_bodySnap_2504_);
                    v_moreSnaps_2505_ = lean_ctor_get(v_val_2501_, 7);
                    lean_inc_ref(v_moreSnaps_2505_);
                    lean_dec(v_val_2501_);
                    if lean_obj_tag(v_tacSnap_x3f_2503_) == 0 {
                        v___x_2518_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0;
                        v___y_2507_ = v___x_2518_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2519_ = lean_ctor_get(v_tacSnap_x3f_2503_, 0);
                        lean_inc(v_val_2519_);
                        lean_dec_ref_known(v_tacSnap_x3f_2503_, 1);
                        v_stx_x3f_2520_ = lean_ctor_get(v_val_2519_, 0);
                        lean_inc(v_stx_x3f_2520_);
                        v_reportingRange_2521_ = lean_ctor_get(v_val_2519_, 1);
                        lean_inc(v_reportingRange_2521_);
                        v___x_2522_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1;
                        v___x_2523_ = 1;
                        v___x_2524_ = l_Lean_Language_SnapshotTask_map___redArg(
                            v_val_2519_,
                            v___x_2522_,
                            v_stx_x3f_2520_,
                            v_reportingRange_2521_,
                            v___x_2523_,
                        );
                        v___x_2525_ = lean_unsigned_to_nat(1);
                        v___x_2526_ = lean_mk_empty_array_with_capacity(v___x_2525_);
                        v___x_2527_ = lean_array_push(v___x_2526_, v___x_2524_);
                        v___y_2507_ = v___x_2527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_2508_ = lean_ctor_get(v_bodySnap_2504_, 0);
                lean_inc(v_stx_x3f_2508_);
                v_reportingRange_2509_ = lean_ctor_get(v_bodySnap_2504_, 1);
                lean_inc(v_reportingRange_2509_);
                v___x_2510_ = 1;
                v___x_2511_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_bodySnap_2504_,
                    v___f_2498_,
                    v_stx_x3f_2508_,
                    v_reportingRange_2509_,
                    v___x_2510_,
                );
                v___x_2512_ = lean_unsigned_to_nat(1);
                v___x_2513_ = lean_mk_empty_array_with_capacity(v___x_2512_);
                v___x_2514_ = lean_array_push(v___x_2513_, v___x_2511_);
                v___x_2515_ = l_Array_append___redArg(v___y_2507_, v___x_2514_);
                lean_dec_ref(v___x_2514_);
                v___x_2516_ = l_Array_append___redArg(v___x_2515_, v_moreSnaps_2505_);
                lean_dec_ref(v_moreSnaps_2505_);
                v___x_2517_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2517_, 0, v_toSnapshot_2502_);
                lean_ctor_set(v___x_2517_, 1, v___x_2516_);
                return v___x_2517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(
    mut v___f_2528_: *mut LeanObject,
    mut v_x_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_headerProcessedSnap_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: u8 = 0;
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    v_headerProcessedSnap_2530_ = lean_ctor_get(v_x_2529_, 1);
    lean_inc_ref(v_headerProcessedSnap_2530_);
    lean_dec_ref(v_x_2529_);
    v_stx_x3f_2531_ = lean_ctor_get(v_headerProcessedSnap_2530_, 0);
    lean_inc(v_stx_x3f_2531_);
    v_reportingRange_2532_ = lean_ctor_get(v_headerProcessedSnap_2530_, 1);
    lean_inc(v_reportingRange_2532_);
    v___x_2533_ = 1;
    v___x_2534_ = l_Lean_Language_SnapshotTask_map___redArg(
        v_headerProcessedSnap_2530_,
        v___f_2528_,
        v_stx_x3f_2531_,
        v_reportingRange_2532_,
        v___x_2533_,
    );
    return v___x_2534_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2(
    mut v___f_2554_: *mut LeanObject,
    mut v_s_2555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSnapshot_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defs_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2560_: u8 = 0;
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2562_: usize = 0;
    let mut v___x_2563_: usize = 0;
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_2556_ = lean_ctor_get(v_s_2555_, 0);
                v_defs_2557_ = lean_ctor_get(v_s_2555_, 1);
                v_isSharedCheck_2568_ = (!lean_is_exclusive(v_s_2555_)) as u8;
                if v_isSharedCheck_2568_ == 0 {
                    v___x_2559_ = v_s_2555_;
                    v_isShared_2560_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_defs_2557_);
                    lean_inc(v_toSnapshot_2556_);
                    lean_dec(v_s_2555_);
                    v___x_2559_ = lean_box(0);
                    v_isShared_2560_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2561_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9;
                v_sz_2562_ = lean_array_size(v_defs_2557_);
                v___x_2563_ = 0usize;
                v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2561_,
                    v___f_2554_,
                    v_sz_2562_,
                    v___x_2563_,
                    v_defs_2557_,
                );
                if v_isShared_2560_ == 0 {
                    lean_ctor_set(v___x_2559_, 1, v___x_2564_);
                    v___x_2566_ = v___x_2559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_toSnapshot_2556_);
                    lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2564_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefView_default___closed__0() -> *mut LeanObject {
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    v___x_2576_ = lean_box(0);
    v___x_2577_ = l_Lean_Elab_instInhabitedModifiers_default;
    v___x_2578_ = lean_box(0);
    v___x_2579_ = 0;
    v___x_2580_ = lean_alloc_ctor(0, 10, (1) as u32);
    lean_ctor_set(v___x_2580_, 0, v___x_2578_);
    lean_ctor_set(v___x_2580_, 1, v___x_2578_);
    lean_ctor_set(v___x_2580_, 2, v___x_2577_);
    lean_ctor_set(v___x_2580_, 3, v___x_2578_);
    lean_ctor_set(v___x_2580_, 4, v___x_2578_);
    lean_ctor_set(v___x_2580_, 5, v___x_2576_);
    lean_ctor_set(v___x_2580_, 6, v___x_2578_);
    lean_ctor_set(v___x_2580_, 7, v___x_2576_);
    lean_ctor_set(v___x_2580_, 8, v___x_2576_);
    lean_ctor_set(v___x_2580_, 9, v___x_2576_);
    lean_ctor_set_uint8(
        v___x_2580_,
        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
        v___x_2579_,
    );
    return v___x_2580_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefView_default() -> *mut LeanObject {
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v___x_2581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefView_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefView_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedDefView_default___closed__0,
    );
    return v___x_2581_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefView() -> *mut LeanObject {
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    v___x_2582_ = l_Lean_Elab_instInhabitedDefView_default;
    return v___x_2582_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(
    mut v_as_2586_: *mut LeanObject,
    mut v_i_2587_: usize,
    mut v_stop_2588_: usize,
) -> u8 {
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: usize = 0;
    let mut v___x_2595_: usize = 0;
    let mut v___x_2597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2589_ = lean_usize_dec_eq(v_i_2587_, v_stop_2588_);
                if v___x_2589_ == 0 {
                    v___x_2590_ = lean_array_uget_borrowed(v_as_2586_, v_i_2587_);
                    v_name_2591_ = lean_ctor_get(v___x_2590_, 0);
                    v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1;
                    v___x_2593_ = lean_name_eq(v_name_2591_, v___x_2592_);
                    if v___x_2593_ == 0 {
                        v___x_2594_ = 1usize;
                        v___x_2595_ = lean_usize_add(v_i_2587_, v___x_2594_);
                        v_i_2587_ = v___x_2595_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2593_;
                    }
                } else {
                    v___x_2597_ = 0;
                    return v___x_2597_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___boxed(
    mut v_as_2598_: *mut LeanObject,
    mut v_i_2599_: *mut LeanObject,
    mut v_stop_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2601_: usize = 0;
    let mut v_stop_boxed_2602_: usize = 0;
    let mut v_res_2603_: u8 = 0;
    let mut v_r_2604_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2601_ = lean_unbox_usize(v_i_2599_);
    lean_dec(v_i_2599_);
    v_stop_boxed_2602_ = lean_unbox_usize(v_stop_2600_);
    lean_dec(v_stop_2600_);
    v_res_2603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_as_2598_, v_i_boxed_2601_, v_stop_boxed_2602_);
    lean_dec_ref(v_as_2598_);
    v_r_2604_ = lean_box((v_res_2603_) as usize);
    return v_r_2604_;
}
pub unsafe fn l_Lean_Elab_DefView_isInstance(mut v_view_2605_: *mut LeanObject) -> u8 {
    let mut v_modifiers_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: u8 = 0;
    v_modifiers_2606_ = lean_ctor_get(v_view_2605_, 2);
    v_attrs_2607_ = lean_ctor_get(v_modifiers_2606_, 2);
    v___x_2608_ = lean_unsigned_to_nat(0);
    v___x_2609_ = lean_array_get_size(v_attrs_2607_);
    v___x_2610_ = lean_nat_dec_lt(v___x_2608_, v___x_2609_);
    if v___x_2610_ == 0 {
        return v___x_2610_;
    } else {
        if v___x_2610_ == 0 {
            return v___x_2610_;
        } else {
            let mut v___x_2611_: usize = 0;
            let mut v___x_2612_: usize = 0;
            let mut v___x_2613_: u8 = 0;
            v___x_2611_ = 0usize;
            v___x_2612_ = lean_usize_of_nat(v___x_2609_);
            v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_attrs_2607_, v___x_2611_, v___x_2612_);
            return v___x_2613_;
        }
    }
}
pub unsafe fn l_Lean_Elab_DefView_isInstance___boxed(
    mut v_view_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2615_: u8 = 0;
    let mut v_r_2616_: *mut LeanObject = core::ptr::null_mut();
    v_res_2615_ = l_Lean_Elab_DefView_isInstance(v_view_2614_);
    lean_dec_ref(v_view_2614_);
    v_r_2616_ = lean_box((v_res_2615_) as usize);
    return v_r_2616_;
}
pub unsafe fn l_Lean_Elab_DefView_markDefEq___lam__0(mut v_x_2620_: *mut LeanObject) -> u8 {
    let mut v_name_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    v_name_2621_ = lean_ctor_get(v_x_2620_, 0);
    v___x_2622_ = l_Lean_Elab_DefView_markDefEq___lam__0___closed__1;
    v___x_2623_ = lean_name_eq(v_name_2621_, v___x_2622_);
    if v___x_2623_ == 0 {
        let mut v___x_2624_: u8 = 0;
        v___x_2624_ = 1;
        return v___x_2624_;
    } else {
        let mut v___x_2625_: u8 = 0;
        v___x_2625_ = 0;
        return v___x_2625_;
    }
}
pub unsafe fn l_Lean_Elab_DefView_markDefEq___lam__0___boxed(
    mut v_x_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2627_: u8 = 0;
    let mut v_r_2628_: *mut LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Lean_Elab_DefView_markDefEq___lam__0(v_x_2626_);
    lean_dec_ref(v_x_2626_);
    v_r_2628_ = lean_box((v_res_2627_) as usize);
    return v_r_2628_;
}
pub unsafe fn l_Lean_Elab_DefView_markDefEq(mut v_view_2634_: *mut LeanObject) -> *mut LeanObject {
    let mut v_kind_2635_: u8 = 0;
    let mut v_ref_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_headerRef_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declId_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_x3f_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_headerSnap_x3f_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deriving_x3f_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2648_: u8 = 0;
    let mut v___f_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_2635_ = lean_ctor_get_uint8(
                    v_view_2634_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_ref_2636_ = lean_ctor_get(v_view_2634_, 0);
                v_headerRef_2637_ = lean_ctor_get(v_view_2634_, 1);
                v_modifiers_2638_ = lean_ctor_get(v_view_2634_, 2);
                v_declId_2639_ = lean_ctor_get(v_view_2634_, 3);
                v_binders_2640_ = lean_ctor_get(v_view_2634_, 4);
                v_type_x3f_2641_ = lean_ctor_get(v_view_2634_, 5);
                v_value_2642_ = lean_ctor_get(v_view_2634_, 6);
                v_docString_x3f_2643_ = lean_ctor_get(v_view_2634_, 7);
                v_headerSnap_x3f_2644_ = lean_ctor_get(v_view_2634_, 8);
                v_deriving_x3f_2645_ = lean_ctor_get(v_view_2634_, 9);
                v_isSharedCheck_2656_ = (!lean_is_exclusive(v_view_2634_)) as u8;
                if v_isSharedCheck_2656_ == 0 {
                    v___x_2647_ = v_view_2634_;
                    v_isShared_2648_ = v_isSharedCheck_2656_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_deriving_x3f_2645_);
                    lean_inc(v_headerSnap_x3f_2644_);
                    lean_inc(v_docString_x3f_2643_);
                    lean_inc(v_value_2642_);
                    lean_inc(v_type_x3f_2641_);
                    lean_inc(v_binders_2640_);
                    lean_inc(v_declId_2639_);
                    lean_inc(v_modifiers_2638_);
                    lean_inc(v_headerRef_2637_);
                    lean_inc(v_ref_2636_);
                    lean_dec(v_view_2634_);
                    v___x_2647_ = lean_box(0);
                    v_isShared_2648_ = v_isSharedCheck_2656_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2649_ = l_Lean_Elab_DefView_markDefEq___closed__0;
                v___x_2650_ = l_Lean_Elab_Modifiers_filterAttrs(v_modifiers_2638_, v___f_2649_);
                v___x_2651_ = l_Lean_Elab_DefView_markDefEq___closed__1;
                v___x_2652_ = l_Lean_Elab_Modifiers_addFirstAttr(v___x_2650_, v___x_2651_);
                if v_isShared_2648_ == 0 {
                    lean_ctor_set(v___x_2647_, 2, v___x_2652_);
                    v___x_2654_ = v___x_2647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_ref_2636_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_headerRef_2637_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 2, v___x_2652_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_declId_2639_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_binders_2640_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 5, v_type_x3f_2641_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 6, v_value_2642_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 7, v_docString_x3f_2643_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 8, v_headerSnap_x3f_2644_);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 9, v_deriving_x3f_2645_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2655_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_kind_2635_,
                    );
                    v___x_2654_ = v_reuseFailAlloc_2655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfAbbrev(
    mut v_modifiers_2674_: *mut LeanObject,
    mut v_stx_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    v___x_2676_ = lean_unsigned_to_nat(2);
    v___x_2677_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2676_);
    v___x_2678_ = l_Lean_Elab_expandOptDeclSig(v___x_2677_);
    lean_dec(v___x_2677_);
    v_fst_2679_ = lean_ctor_get(v___x_2678_, 0);
    lean_inc(v_fst_2679_);
    v_snd_2680_ = lean_ctor_get(v___x_2678_, 1);
    lean_inc(v_snd_2680_);
    lean_dec_ref(v___x_2678_);
    v___x_2681_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2;
    v_modifiers_2682_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_2674_, v___x_2681_);
    v___x_2683_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5;
    v_modifiers_2684_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_2682_, v___x_2683_);
    v_docString_x3f_2685_ = lean_ctor_get(v_modifiers_2684_, 1);
    lean_inc(v_docString_x3f_2685_);
    v___x_2686_ = 5;
    v___x_2687_ = l_Lean_Syntax_getArgs(v_stx_2675_);
    v___x_2688_ = lean_unsigned_to_nat(3);
    v___x_2689_ = lean_unsigned_to_nat(0);
    v___x_2690_ = l_Array_toSubarray___redArg(v___x_2687_, v___x_2689_, v___x_2688_);
    v___x_2691_ = l_Subarray_copy___redArg(v___x_2690_);
    v___x_2692_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
    v___x_2693_ = lean_box(2);
    v___x_2694_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2694_, 0, v___x_2693_);
    lean_ctor_set(v___x_2694_, 1, v___x_2692_);
    lean_ctor_set(v___x_2694_, 2, v___x_2691_);
    v___x_2695_ = lean_unsigned_to_nat(1);
    v___x_2696_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2695_);
    v___x_2697_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2688_);
    v___x_2698_ = lean_box(0);
    v___x_2699_ = lean_alloc_ctor(0, 10, (1) as u32);
    lean_ctor_set(v___x_2699_, 0, v_stx_2675_);
    lean_ctor_set(v___x_2699_, 1, v___x_2694_);
    lean_ctor_set(v___x_2699_, 2, v_modifiers_2684_);
    lean_ctor_set(v___x_2699_, 3, v___x_2696_);
    lean_ctor_set(v___x_2699_, 4, v_fst_2679_);
    lean_ctor_set(v___x_2699_, 5, v_snd_2680_);
    lean_ctor_set(v___x_2699_, 6, v___x_2697_);
    lean_ctor_set(v___x_2699_, 7, v_docString_x3f_2685_);
    lean_ctor_set(v___x_2699_, 8, v___x_2698_);
    lean_ctor_set(v___x_2699_, 9, v___x_2698_);
    lean_ctor_set_uint8(
        v___x_2699_,
        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
        v___x_2686_,
    );
    return v___x_2699_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfDef(
    mut v_modifiers_2700_: *mut LeanObject,
    mut v_stx_2701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: u8 = 0;
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2702_ = lean_unsigned_to_nat(2);
                v___x_2703_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2702_);
                v___x_2704_ = l_Lean_Elab_expandOptDeclSig(v___x_2703_);
                lean_dec(v___x_2703_);
                v_fst_2705_ = lean_ctor_get(v___x_2704_, 0);
                lean_inc(v_fst_2705_);
                v_snd_2706_ = lean_ctor_get(v___x_2704_, 1);
                lean_inc(v_snd_2706_);
                lean_dec_ref(v___x_2704_);
                v___x_2724_ = lean_unsigned_to_nat(4);
                v___x_2725_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2724_);
                v___x_2726_ = l_Lean_Syntax_isNone(v___x_2725_);
                if v___x_2726_ == 0 {
                    v___x_2727_ = lean_unsigned_to_nat(1);
                    v___x_2728_ = l_Lean_Syntax_getArg(v___x_2725_, v___x_2727_);
                    lean_dec(v___x_2725_);
                    v___x_2729_ = l_Lean_Syntax_getSepArgs(v___x_2728_);
                    lean_dec(v___x_2728_);
                    v___x_2730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2730_, 0, v___x_2729_);
                    v___y_2708_ = v___x_2730_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_2725_);
                    v___x_2731_ = lean_box(0);
                    v___y_2708_ = v___x_2731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_docString_x3f_2709_ = lean_ctor_get(v_modifiers_2700_, 1);
                lean_inc(v_docString_x3f_2709_);
                v___x_2710_ = 0;
                v___x_2711_ = l_Lean_Syntax_getArgs(v_stx_2701_);
                v___x_2712_ = lean_unsigned_to_nat(3);
                v___x_2713_ = lean_unsigned_to_nat(0);
                v___x_2714_ = l_Array_toSubarray___redArg(v___x_2711_, v___x_2713_, v___x_2712_);
                v___x_2715_ = l_Subarray_copy___redArg(v___x_2714_);
                v___x_2716_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_2717_ = lean_box(2);
                v___x_2718_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2718_, 0, v___x_2717_);
                lean_ctor_set(v___x_2718_, 1, v___x_2716_);
                lean_ctor_set(v___x_2718_, 2, v___x_2715_);
                v___x_2719_ = lean_unsigned_to_nat(1);
                v___x_2720_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2719_);
                v___x_2721_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2712_);
                v___x_2722_ = lean_box(0);
                v___x_2723_ = lean_alloc_ctor(0, 10, (1) as u32);
                lean_ctor_set(v___x_2723_, 0, v_stx_2701_);
                lean_ctor_set(v___x_2723_, 1, v___x_2718_);
                lean_ctor_set(v___x_2723_, 2, v_modifiers_2700_);
                lean_ctor_set(v___x_2723_, 3, v___x_2720_);
                lean_ctor_set(v___x_2723_, 4, v_fst_2705_);
                lean_ctor_set(v___x_2723_, 5, v_snd_2706_);
                lean_ctor_set(v___x_2723_, 6, v___x_2721_);
                lean_ctor_set(v___x_2723_, 7, v_docString_x3f_2709_);
                lean_ctor_set(v___x_2723_, 8, v___x_2722_);
                lean_ctor_set(v___x_2723_, 9, v___y_2708_);
                lean_ctor_set_uint8(
                    v___x_2723_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    v___x_2710_,
                );
                return v___x_2723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfTheorem(
    mut v_modifiers_2732_: *mut LeanObject,
    mut v_stx_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    v___x_2734_ = lean_unsigned_to_nat(2);
    v___x_2735_ = l_Lean_Syntax_getArg(v_stx_2733_, v___x_2734_);
    v___x_2736_ = l_Lean_Elab_expandDeclSig(v___x_2735_);
    lean_dec(v___x_2735_);
    v_fst_2737_ = lean_ctor_get(v___x_2736_, 0);
    lean_inc(v_fst_2737_);
    v_snd_2738_ = lean_ctor_get(v___x_2736_, 1);
    lean_inc(v_snd_2738_);
    lean_dec_ref(v___x_2736_);
    v_docString_x3f_2739_ = lean_ctor_get(v_modifiers_2732_, 1);
    lean_inc(v_docString_x3f_2739_);
    v___x_2740_ = 2;
    v___x_2741_ = l_Lean_Syntax_getArgs(v_stx_2733_);
    v___x_2742_ = lean_unsigned_to_nat(3);
    v___x_2743_ = lean_unsigned_to_nat(0);
    v___x_2744_ = l_Array_toSubarray___redArg(v___x_2741_, v___x_2743_, v___x_2742_);
    v___x_2745_ = l_Subarray_copy___redArg(v___x_2744_);
    v___x_2746_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
    v___x_2747_ = lean_box(2);
    v___x_2748_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2748_, 0, v___x_2747_);
    lean_ctor_set(v___x_2748_, 1, v___x_2746_);
    lean_ctor_set(v___x_2748_, 2, v___x_2745_);
    v___x_2749_ = lean_unsigned_to_nat(1);
    v___x_2750_ = l_Lean_Syntax_getArg(v_stx_2733_, v___x_2749_);
    v___x_2751_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2751_, 0, v_snd_2738_);
    v___x_2752_ = l_Lean_Syntax_getArg(v_stx_2733_, v___x_2742_);
    v___x_2753_ = lean_box(0);
    v___x_2754_ = lean_alloc_ctor(0, 10, (1) as u32);
    lean_ctor_set(v___x_2754_, 0, v_stx_2733_);
    lean_ctor_set(v___x_2754_, 1, v___x_2748_);
    lean_ctor_set(v___x_2754_, 2, v_modifiers_2732_);
    lean_ctor_set(v___x_2754_, 3, v___x_2750_);
    lean_ctor_set(v___x_2754_, 4, v_fst_2737_);
    lean_ctor_set(v___x_2754_, 5, v___x_2751_);
    lean_ctor_set(v___x_2754_, 6, v___x_2752_);
    lean_ctor_set(v___x_2754_, 7, v_docString_x3f_2739_);
    lean_ctor_set(v___x_2754_, 8, v___x_2753_);
    lean_ctor_set(v___x_2754_, 9, v___x_2753_);
    lean_ctor_set_uint8(
        v___x_2754_,
        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
        v___x_2740_,
    );
    return v___x_2754_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(
    mut v___y_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    v___x_2757_ = lean_st_ref_get(v___y_2755_);
    v_env_2758_ = lean_ctor_get(v___x_2757_, 0);
    lean_inc_ref(v_env_2758_);
    lean_dec(v___x_2757_);
    v___x_2759_ = l_Lean_Environment_header(v_env_2758_);
    lean_dec_ref(v_env_2758_);
    v_mainModule_2760_ = lean_ctor_get(v___x_2759_, 0);
    lean_inc(v_mainModule_2760_);
    lean_dec_ref(v___x_2759_);
    v___x_2761_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2761_, 0, v_mainModule_2760_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg___boxed(
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2764_: *mut LeanObject = core::ptr::null_mut();
    v_res_2764_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(
            v___y_2762_,
        );
    lean_dec(v___y_2762_);
    return v_res_2764_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(
    mut v___y_2765_: *mut LeanObject,
    mut v___y_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    v___x_2768_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(
            v___y_2766_,
        );
    return v___x_2768_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2772_: *mut LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(
        v___y_2769_,
        v___y_2770_,
    );
    lean_dec(v___y_2770_);
    lean_dec_ref(v___y_2769_);
    return v_res_2772_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Lean_maxRecDepthErrorMessage;
    v___x_2779_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2779_, 0, v___x_2778_);
    return v___x_2779_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    v___x_2780_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3);
    v___x_2781_ = l_Lean_MessageData_ofFormat(v___x_2780_);
    return v___x_2781_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    v___x_2782_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4);
    v___x_2783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2;
    v___x_2784_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_2784_, 0, v___x_2783_);
    lean_ctor_set(v___x_2784_, 1, v___x_2782_);
    return v___x_2784_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(
    mut v_ref_2785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    v___x_2787_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5);
    v___x_2788_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2788_, 0, v_ref_2785_);
    lean_ctor_set(v___x_2788_, 1, v___x_2787_);
    v___x_2789_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2789_, 0, v___x_2788_);
    return v___x_2789_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(
    mut v_ref_2790_: *mut LeanObject,
    mut v___y_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2792_: *mut LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_2790_);
    return v_res_2792_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(
    mut v_x_2793_: *mut LeanObject,
    mut v___y_2794_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2793_) == 0 {
        let mut v_a_2795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
        v_a_2795_ = lean_ctor_get(v_x_2793_, 0);
        lean_inc(v_a_2795_);
        v___x_2796_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2796_, 0, v_a_2795_);
        lean_ctor_set(v___x_2796_, 1, v___y_2794_);
        return v___x_2796_;
    } else {
        let mut v_a_2797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
        v_a_2797_ = lean_ctor_get(v_x_2793_, 0);
        lean_inc(v_a_2797_);
        v___x_2798_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2798_, 0, v_a_2797_);
        lean_ctor_set(v___x_2798_, 1, v___y_2794_);
        return v___x_2798_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(
    mut v_x_2799_: *mut LeanObject,
    mut v___y_2800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2801_: *mut LeanObject = core::ptr::null_mut();
    v_res_2801_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_2799_, v___y_2800_);
    lean_dec_ref(v_x_2799_);
    return v_res_2801_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(
    mut v_env_2802_: *mut LeanObject,
    mut v_stx_2803_: *mut LeanObject,
    mut v___y_2804_: *mut LeanObject,
    mut v___y_2805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_unused_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v_snd_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v_a_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v_a_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2806_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_2802_,
                    v_stx_2803_,
                    v___y_2804_,
                    v___y_2805_,
                );
                if lean_obj_tag(v___x_2806_) == 0 {
                    v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
                    lean_inc(v_a_2807_);
                    if lean_obj_tag(v_a_2807_) == 0 {
                        v_a_2808_ = lean_ctor_get(v___x_2806_, 1);
                        v_isSharedCheck_2816_ = (!lean_is_exclusive(v___x_2806_)) as u8;
                        if v_isSharedCheck_2816_ == 0 {
                            v_unused_2817_ = lean_ctor_get(v___x_2806_, 0);
                            lean_dec(v_unused_2817_);
                            v___x_2810_ = v___x_2806_;
                            v_isShared_2811_ = v_isSharedCheck_2816_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2808_);
                            lean_dec(v___x_2806_);
                            v___x_2810_ = lean_box(0);
                            v_isShared_2811_ = v_isSharedCheck_2816_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_2818_ = lean_ctor_get(v_a_2807_, 0);
                        v_isSharedCheck_2846_ = (!lean_is_exclusive(v_a_2807_)) as u8;
                        if v_isSharedCheck_2846_ == 0 {
                            v___x_2820_ = v_a_2807_;
                            v_isShared_2821_ = v_isSharedCheck_2846_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2818_);
                            lean_dec(v_a_2807_);
                            v___x_2820_ = lean_box(0);
                            v_isShared_2821_ = v_isSharedCheck_2846_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2847_ = lean_ctor_get(v___x_2806_, 0);
                    v_a_2848_ = lean_ctor_get(v___x_2806_, 1);
                    v_isSharedCheck_2855_ = (!lean_is_exclusive(v___x_2806_)) as u8;
                    if v_isSharedCheck_2855_ == 0 {
                        v___x_2850_ = v___x_2806_;
                        v_isShared_2851_ = v_isSharedCheck_2855_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2848_);
                        lean_inc(v_a_2847_);
                        lean_dec(v___x_2806_);
                        v___x_2850_ = lean_box(0);
                        v_isShared_2851_ = v_isSharedCheck_2855_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2812_ = lean_box(0);
                if v_isShared_2811_ == 0 {
                    lean_ctor_set(v___x_2810_, 0, v___x_2812_);
                    v___x_2814_ = v___x_2810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_a_2808_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2814_;
            }
            3 => {
                v_snd_2822_ = lean_ctor_get(v_val_2818_, 1);
                lean_inc(v_snd_2822_);
                lean_dec(v_val_2818_);
                if lean_obj_tag(v_snd_2822_) == 0 {
                    lean_del_object(v___x_2820_);
                    v_a_2823_ = lean_ctor_get(v___x_2806_, 1);
                    lean_inc(v_a_2823_);
                    lean_dec_ref_known(v___x_2806_, 2);
                    v_a_2824_ = lean_ctor_get(v_snd_2822_, 0);
                    v_isSharedCheck_2832_ = (!lean_is_exclusive(v_snd_2822_)) as u8;
                    if v_isSharedCheck_2832_ == 0 {
                        v___x_2826_ = v_snd_2822_;
                        v_isShared_2827_ = v_isSharedCheck_2832_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2824_);
                        lean_dec(v_snd_2822_);
                        v___x_2826_ = lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2832_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2833_ = lean_ctor_get(v___x_2806_, 1);
                    lean_inc(v_a_2833_);
                    lean_dec_ref_known(v___x_2806_, 2);
                    v_a_2834_ = lean_ctor_get(v_snd_2822_, 0);
                    v_isSharedCheck_2845_ = (!lean_is_exclusive(v_snd_2822_)) as u8;
                    if v_isSharedCheck_2845_ == 0 {
                        v___x_2836_ = v_snd_2822_;
                        v_isShared_2837_ = v_isSharedCheck_2845_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2834_);
                        lean_dec(v_snd_2822_);
                        v___x_2836_ = lean_box(0);
                        v_isShared_2837_ = v_isSharedCheck_2845_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2827_ == 0 {
                    v___x_2829_ = v___x_2826_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2824_);
                    v___x_2829_ = v_reuseFailAlloc_2831_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2830_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_2829_, v_a_2823_);
                lean_dec_ref(v___x_2829_);
                return v___x_2830_;
            }
            6 => {
                if v_isShared_2821_ == 0 {
                    lean_ctor_set(v___x_2820_, 0, v_a_2834_);
                    v___x_2839_ = v___x_2820_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2834_);
                    v___x_2839_ = v_reuseFailAlloc_2844_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2837_ == 0 {
                    lean_ctor_set(v___x_2836_, 0, v___x_2839_);
                    v___x_2841_ = v___x_2836_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2839_);
                    v___x_2841_ = v_reuseFailAlloc_2843_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2842_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_2841_, v_a_2833_);
                lean_dec_ref(v___x_2841_);
                return v___x_2842_;
            }
            9 => {
                if v_isShared_2851_ == 0 {
                    v___x_2853_ = v___x_2850_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2847_);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_a_2848_);
                    v___x_2853_ = v_reuseFailAlloc_2854_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(
    mut v_env_2856_: *mut LeanObject,
    mut v_stx_2857_: *mut LeanObject,
    mut v___y_2858_: *mut LeanObject,
    mut v___y_2859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2860_: *mut LeanObject = core::ptr::null_mut();
    v_res_2860_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(v_env_2856_, v_stx_2857_, v___y_2858_, v___y_2859_);
    lean_dec_ref(v___y_2858_);
    return v_res_2860_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(
    mut v_env_2861_: *mut LeanObject,
    mut v_currNamespace_2862_: *mut LeanObject,
    mut v_openDecls_2863_: *mut LeanObject,
    mut v_n_2864_: *mut LeanObject,
    mut v___y_2865_: *mut LeanObject,
    mut v___y_2866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    v___x_2867_ = l_Lean_ResolveName_resolveNamespace(
        v_env_2861_,
        v_currNamespace_2862_,
        v_openDecls_2863_,
        v_n_2864_,
    );
    v___x_2868_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2868_, 0, v___x_2867_);
    lean_ctor_set(v___x_2868_, 1, v___y_2866_);
    return v___x_2868_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(
    mut v_env_2869_: *mut LeanObject,
    mut v_currNamespace_2870_: *mut LeanObject,
    mut v_openDecls_2871_: *mut LeanObject,
    mut v_n_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2875_: *mut LeanObject = core::ptr::null_mut();
    v_res_2875_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(v_env_2869_, v_currNamespace_2870_, v_openDecls_2871_, v_n_2872_, v___y_2873_, v___y_2874_);
    lean_dec_ref(v___y_2873_);
    return v_res_2875_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(
    mut v_currNamespace_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
    mut v___y_2878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    v___x_2879_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2879_, 0, v_currNamespace_2876_);
    lean_ctor_set(v___x_2879_, 1, v___y_2878_);
    return v___x_2879_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(
    mut v_currNamespace_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
    mut v___y_2882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2883_: *mut LeanObject = core::ptr::null_mut();
    v_res_2883_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(v_currNamespace_2880_, v___y_2881_, v___y_2882_);
    lean_dec_ref(v___y_2881_);
    return v_res_2883_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    v___x_2884_ = lean_box(0);
    v___x_2885_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2886_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2886_, 0, v___x_2885_);
    lean_ctor_set(v___x_2886_, 1, v___x_2884_);
    return v___x_2886_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg()
-> *mut LeanObject {
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    v___x_2888_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0);
    v___x_2889_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2889_, 0, v___x_2888_);
    return v___x_2889_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(
    mut v___y_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2891_: *mut LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
    return v_res_2891_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    v___x_2892_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2892_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    v___x_2893_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0);
    v___x_2894_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2894_, 0, v___x_2893_);
    return v___x_2894_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    v___x_2895_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
    v___x_2896_ = lean_unsigned_to_nat(0);
    v___x_2897_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2897_, 0, v___x_2896_);
    lean_ctor_set(v___x_2897_, 1, v___x_2896_);
    lean_ctor_set(v___x_2897_, 2, v___x_2896_);
    lean_ctor_set(v___x_2897_, 3, v___x_2896_);
    lean_ctor_set(v___x_2897_, 4, v___x_2895_);
    lean_ctor_set(v___x_2897_, 5, v___x_2895_);
    lean_ctor_set(v___x_2897_, 6, v___x_2895_);
    lean_ctor_set(v___x_2897_, 7, v___x_2895_);
    lean_ctor_set(v___x_2897_, 8, v___x_2895_);
    lean_ctor_set(v___x_2897_, 9, v___x_2895_);
    return v___x_2897_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    v___x_2898_ = lean_unsigned_to_nat(32);
    v___x_2899_ = lean_mk_empty_array_with_capacity(v___x_2898_);
    v___x_2900_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2900_, 0, v___x_2899_);
    return v___x_2900_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2901_: usize = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    v___x_2901_ = 5usize;
    v___x_2902_ = lean_unsigned_to_nat(0);
    v___x_2903_ = lean_unsigned_to_nat(32);
    v___x_2904_ = lean_mk_empty_array_with_capacity(v___x_2903_);
    v___x_2905_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3);
    v___x_2906_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2906_, 0, v___x_2905_);
    lean_ctor_set(v___x_2906_, 1, v___x_2904_);
    lean_ctor_set(v___x_2906_, 2, v___x_2902_);
    lean_ctor_set(v___x_2906_, 3, v___x_2902_);
    lean_ctor_set_usize(v___x_2906_, 4, v___x_2901_);
    return v___x_2906_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    v___x_2907_ = lean_box(1);
    v___x_2908_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4);
    v___x_2909_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
    v___x_2910_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2910_, 0, v___x_2909_);
    lean_ctor_set(v___x_2910_, 1, v___x_2908_);
    lean_ctor_set(v___x_2910_, 2, v___x_2907_);
    return v___x_2910_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(
    mut v_msgData_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ = lean_st_ref_get(v___y_2912_);
    v_env_2915_ = lean_ctor_get(v___x_2914_, 0);
    lean_inc_ref(v_env_2915_);
    lean_dec(v___x_2914_);
    v___x_2916_ = lean_st_ref_get(v___y_2912_);
    v_scopes_2917_ = lean_ctor_get(v___x_2916_, 2);
    lean_inc(v_scopes_2917_);
    lean_dec(v___x_2916_);
    v___x_2918_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2919_ = l_List_head_x21___redArg(v___x_2918_, v_scopes_2917_);
    lean_dec(v_scopes_2917_);
    v_opts_2920_ = lean_ctor_get(v___x_2919_, 1);
    lean_inc_ref(v_opts_2920_);
    lean_dec(v___x_2919_);
    v___x_2921_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2);
    v___x_2922_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5);
    v___x_2923_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2923_, 0, v_env_2915_);
    lean_ctor_set(v___x_2923_, 1, v___x_2921_);
    lean_ctor_set(v___x_2923_, 2, v___x_2922_);
    lean_ctor_set(v___x_2923_, 3, v_opts_2920_);
    v___x_2924_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2924_, 0, v___x_2923_);
    lean_ctor_set(v___x_2924_, 1, v_msgData_2911_);
    v___x_2925_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2925_, 0, v___x_2924_);
    return v___x_2925_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___boxed(
    mut v_msgData_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
    mut v___y_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2929_: *mut LeanObject = core::ptr::null_mut();
    v_res_2929_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_2926_, v___y_2927_);
    lean_dec(v___y_2927_);
    return v_res_2929_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0()
-> f64 {
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: f64 = 0.0;
    v___x_2930_ = lean_unsigned_to_nat(0);
    v___x_2931_ = lean_float_of_nat(v___x_2930_);
    return v___x_2931_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(
    mut v_cls_2935_: *mut LeanObject,
    mut v_msg_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v_tid_2962_: u64 = 0;
    let mut v_traces_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: f64 = 0.0;
    let mut v___x_2969_: u8 = 0;
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_isSharedCheck_2988_: u8 = 0;
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_a_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2940_ = l_Lean_Elab_Command_getRef___redArg(v___y_2937_);
                if lean_obj_tag(v___x_2940_) == 0 {
                    v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
                    lean_inc(v_a_2941_);
                    lean_dec_ref_known(v___x_2940_, 1);
                    v___x_2942_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_2936_, v___y_2938_);
                    v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
                    v_isSharedCheck_2989_ = (!lean_is_exclusive(v___x_2942_)) as u8;
                    if v_isSharedCheck_2989_ == 0 {
                        v___x_2945_ = v___x_2942_;
                        v_isShared_2946_ = v_isSharedCheck_2989_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2943_);
                        lean_dec(v___x_2942_);
                        v___x_2945_ = lean_box(0);
                        v_isShared_2946_ = v_isSharedCheck_2989_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_2936_);
                    lean_dec(v_cls_2935_);
                    v_a_2990_ = lean_ctor_get(v___x_2940_, 0);
                    v_isSharedCheck_2997_ = (!lean_is_exclusive(v___x_2940_)) as u8;
                    if v_isSharedCheck_2997_ == 0 {
                        v___x_2992_ = v___x_2940_;
                        v_isShared_2993_ = v_isSharedCheck_2997_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2990_);
                        lean_dec(v___x_2940_);
                        v___x_2992_ = lean_box(0);
                        v_isShared_2993_ = v_isSharedCheck_2997_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2947_ = lean_st_ref_take(v___y_2938_);
                v_traceState_2948_ = lean_ctor_get(v___x_2947_, 9);
                v_env_2949_ = lean_ctor_get(v___x_2947_, 0);
                v_messages_2950_ = lean_ctor_get(v___x_2947_, 1);
                v_scopes_2951_ = lean_ctor_get(v___x_2947_, 2);
                v_usedQuotCtxts_2952_ = lean_ctor_get(v___x_2947_, 3);
                v_nextMacroScope_2953_ = lean_ctor_get(v___x_2947_, 4);
                v_maxRecDepth_2954_ = lean_ctor_get(v___x_2947_, 5);
                v_ngen_2955_ = lean_ctor_get(v___x_2947_, 6);
                v_auxDeclNGen_2956_ = lean_ctor_get(v___x_2947_, 7);
                v_infoState_2957_ = lean_ctor_get(v___x_2947_, 8);
                v_snapshotTasks_2958_ = lean_ctor_get(v___x_2947_, 10);
                v_isSharedCheck_2988_ = (!lean_is_exclusive(v___x_2947_)) as u8;
                if v_isSharedCheck_2988_ == 0 {
                    v___x_2960_ = v___x_2947_;
                    v_isShared_2961_ = v_isSharedCheck_2988_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2958_);
                    lean_inc(v_traceState_2948_);
                    lean_inc(v_infoState_2957_);
                    lean_inc(v_auxDeclNGen_2956_);
                    lean_inc(v_ngen_2955_);
                    lean_inc(v_maxRecDepth_2954_);
                    lean_inc(v_nextMacroScope_2953_);
                    lean_inc(v_usedQuotCtxts_2952_);
                    lean_inc(v_scopes_2951_);
                    lean_inc(v_messages_2950_);
                    lean_inc(v_env_2949_);
                    lean_dec(v___x_2947_);
                    v___x_2960_ = lean_box(0);
                    v_isShared_2961_ = v_isSharedCheck_2988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2962_ = lean_ctor_get_uint64(
                    v_traceState_2948_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2963_ = lean_ctor_get(v_traceState_2948_, 0);
                v_isSharedCheck_2987_ = (!lean_is_exclusive(v_traceState_2948_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v___x_2965_ = v_traceState_2948_;
                    v_isShared_2966_ = v_isSharedCheck_2987_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2963_);
                    lean_dec(v_traceState_2948_);
                    v___x_2965_ = lean_box(0);
                    v_isShared_2966_ = v_isSharedCheck_2987_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2967_ = lean_box(0);
                v___x_2968_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0);
                v___x_2969_ = 0;
                v___x_2970_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1;
                v___x_2971_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2971_, 0, v_cls_2935_);
                lean_ctor_set(v___x_2971_, 1, v___x_2967_);
                lean_ctor_set(v___x_2971_, 2, v___x_2970_);
                lean_ctor_set_float(
                    v___x_2971_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2968_,
                );
                lean_ctor_set_float(
                    v___x_2971_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2968_,
                );
                lean_ctor_set_uint8(
                    v___x_2971_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2969_,
                );
                v___x_2972_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2;
                v___x_2973_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2973_, 0, v___x_2971_);
                lean_ctor_set(v___x_2973_, 1, v_a_2943_);
                lean_ctor_set(v___x_2973_, 2, v___x_2972_);
                v___x_2974_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2974_, 0, v_a_2941_);
                lean_ctor_set(v___x_2974_, 1, v___x_2973_);
                v___x_2975_ = l_Lean_PersistentArray_push___redArg(v_traces_2963_, v___x_2974_);
                if v_isShared_2966_ == 0 {
                    lean_ctor_set(v___x_2965_, 0, v___x_2975_);
                    v___x_2977_ = v___x_2965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2975_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2986_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2962_,
                    );
                    v___x_2977_ = v_reuseFailAlloc_2986_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2961_ == 0 {
                    lean_ctor_set(v___x_2960_, 9, v___x_2977_);
                    v___x_2979_ = v___x_2960_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_env_2949_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_messages_2950_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_scopes_2951_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_usedQuotCtxts_2952_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_nextMacroScope_2953_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 5, v_maxRecDepth_2954_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 6, v_ngen_2955_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 7, v_auxDeclNGen_2956_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 8, v_infoState_2957_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 9, v___x_2977_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 10, v_snapshotTasks_2958_);
                    v___x_2979_ = v_reuseFailAlloc_2985_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2980_ = lean_st_ref_set(v___y_2938_, v___x_2979_);
                v___x_2981_ = lean_box(0);
                if v_isShared_2946_ == 0 {
                    lean_ctor_set(v___x_2945_, 0, v___x_2981_);
                    v___x_2983_ = v___x_2945_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
                    v___x_2983_ = v_reuseFailAlloc_2984_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2983_;
            }
            7 => {
                if v_isShared_2993_ == 0 {
                    v___x_2995_ = v___x_2992_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
                    v___x_2995_ = v_reuseFailAlloc_2996_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(
    mut v_cls_2998_: *mut LeanObject,
    mut v_msg_2999_: *mut LeanObject,
    mut v___y_3000_: *mut LeanObject,
    mut v___y_3001_: *mut LeanObject,
    mut v___y_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3003_: *mut LeanObject = core::ptr::null_mut();
    v_res_3003_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(
        v_cls_2998_,
        v_msg_2999_,
        v___y_3000_,
        v___y_3001_,
    );
    lean_dec(v___y_3001_);
    lean_dec_ref(v___y_3000_);
    return v_res_3003_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(
    mut v_keys_3004_: *mut LeanObject,
    mut v_i_3005_: *mut LeanObject,
    mut v_k_3006_: *mut LeanObject,
) -> u8 {
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v_k_x27_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: u8 = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3007_ = lean_array_get_size(v_keys_3004_);
                v___x_3008_ = lean_nat_dec_lt(v_i_3005_, v___x_3007_);
                if v___x_3008_ == 0 {
                    lean_dec(v_i_3005_);
                    return v___x_3008_;
                } else {
                    v_k_x27_3009_ = lean_array_fget_borrowed(v_keys_3004_, v_i_3005_);
                    v___x_3010_ = l_Lean_instBEqExtraModUse_beq(v_k_3006_, v_k_x27_3009_);
                    if v___x_3010_ == 0 {
                        v___x_3011_ = lean_unsigned_to_nat(1);
                        v___x_3012_ = lean_nat_add(v_i_3005_, v___x_3011_);
                        lean_dec(v_i_3005_);
                        v_i_3005_ = v___x_3012_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_3005_);
                        return v___x_3010_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(
    mut v_keys_3014_: *mut LeanObject,
    mut v_i_3015_: *mut LeanObject,
    mut v_k_3016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3017_: u8 = 0;
    let mut v_r_3018_: *mut LeanObject = core::ptr::null_mut();
    v_res_3017_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_3014_, v_i_3015_, v_k_3016_);
    lean_dec_ref(v_k_3016_);
    lean_dec_ref(v_keys_3014_);
    v_r_3018_ = lean_box((v_res_3017_) as usize);
    return v_r_3018_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0()
-> usize {
    let mut v___x_3019_: usize = 0;
    let mut v___x_3020_: usize = 0;
    let mut v___x_3021_: usize = 0;
    v___x_3019_ = 5usize;
    v___x_3020_ = 1usize;
    v___x_3021_ = lean_usize_shift_left(v___x_3020_, v___x_3019_);
    return v___x_3021_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1()
-> usize {
    let mut v___x_3022_: usize = 0;
    let mut v___x_3023_: usize = 0;
    let mut v___x_3024_: usize = 0;
    v___x_3022_ = 1usize;
    v___x_3023_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0);
    v___x_3024_ = lean_usize_sub(v___x_3023_, v___x_3022_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(
    mut v_x_3025_: *mut LeanObject,
    mut v_x_3026_: usize,
    mut v_x_3027_: *mut LeanObject,
) -> u8 {
    let mut v_es_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: usize = 0;
    let mut v___x_3031_: usize = 0;
    let mut v___x_3032_: usize = 0;
    let mut v_j_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: u8 = 0;
    let mut v_node_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: usize = 0;
    let mut v___x_3040_: u8 = 0;
    let mut v_ks_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3025_) == 0 {
                    v_es_3028_ = lean_ctor_get(v_x_3025_, 0);
                    v___x_3029_ = lean_box(2);
                    v___x_3030_ = 5usize;
                    v___x_3031_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1);
                    v___x_3032_ = lean_usize_land(v_x_3026_, v___x_3031_);
                    v_j_3033_ = lean_usize_to_nat(v___x_3032_);
                    v___x_3034_ = lean_array_get_borrowed(v___x_3029_, v_es_3028_, v_j_3033_);
                    lean_dec(v_j_3033_);
                    match lean_obj_tag(v___x_3034_) {
                        0 => {
                            v_key_3035_ = lean_ctor_get(v___x_3034_, 0);
                            v___x_3036_ = l_Lean_instBEqExtraModUse_beq(v_x_3027_, v_key_3035_);
                            return v___x_3036_;
                        }
                        1 => {
                            v_node_3037_ = lean_ctor_get(v___x_3034_, 0);
                            v___x_3038_ = lean_usize_shift_right(v_x_3026_, v___x_3030_);
                            v_x_3025_ = v_node_3037_;
                            v_x_3026_ = v___x_3038_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3040_ = 0;
                            return v___x_3040_;
                        }
                    }
                } else {
                    v_ks_3041_ = lean_ctor_get(v_x_3025_, 0);
                    v___x_3042_ = lean_unsigned_to_nat(0);
                    v___x_3043_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_ks_3041_, v___x_3042_, v_x_3027_);
                    return v___x_3043_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(
    mut v_x_3044_: *mut LeanObject,
    mut v_x_3045_: *mut LeanObject,
    mut v_x_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_16987__boxed_3047_: usize = 0;
    let mut v_res_3048_: u8 = 0;
    let mut v_r_3049_: *mut LeanObject = core::ptr::null_mut();
    v_x_16987__boxed_3047_ = lean_unbox_usize(v_x_3045_);
    lean_dec(v_x_3045_);
    v_res_3048_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3044_, v_x_16987__boxed_3047_, v_x_3046_);
    lean_dec_ref(v_x_3046_);
    lean_dec_ref(v_x_3044_);
    v_r_3049_ = lean_box((v_res_3048_) as usize);
    return v_r_3049_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(
    mut v_x_3050_: *mut LeanObject,
    mut v_x_3051_: *mut LeanObject,
) -> u8 {
    let mut v___x_3052_: u64 = 0;
    let mut v___x_3053_: usize = 0;
    let mut v___x_3054_: u8 = 0;
    v___x_3052_ = l_Lean_instHashableExtraModUse_hash(v_x_3051_);
    v___x_3053_ = lean_uint64_to_usize(v___x_3052_);
    v___x_3054_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3050_, v___x_3053_, v_x_3051_);
    return v___x_3054_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_x_3055_: *mut LeanObject,
    mut v_x_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3057_: u8 = 0;
    let mut v_r_3058_: *mut LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_3055_, v_x_3056_);
    lean_dec_ref(v_x_3056_);
    lean_dec_ref(v_x_3055_);
    v_r_3058_ = lean_box((v_res_3057_) as usize);
    return v_r_3058_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    v___x_3061_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1;
    v___x_3062_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0;
    v___x_3063_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3062_, v___x_3061_);
    return v___x_3063_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6()
-> *mut LeanObject {
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    v___x_3068_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5;
    v___x_3069_ = l_Lean_stringToMessageData(v___x_3068_);
    return v___x_3069_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8()
-> *mut LeanObject {
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    v___x_3071_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7;
    v___x_3072_ = l_Lean_stringToMessageData(v___x_3071_);
    return v___x_3072_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9()
-> *mut LeanObject {
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    v___x_3073_ =
        l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1;
    v___x_3074_ = l_Lean_stringToMessageData(v___x_3073_);
    return v___x_3074_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12()
-> *mut LeanObject {
    let mut v_cls_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    v_cls_3078_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4;
    v___x_3079_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11;
    v___x_3080_ = l_Lean_Name_append(v___x_3079_, v_cls_3078_);
    return v___x_3080_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14()
-> *mut LeanObject {
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    v___x_3082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13;
    v___x_3083_ = l_Lean_stringToMessageData(v___x_3082_);
    return v___x_3083_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16()
-> *mut LeanObject {
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    v___x_3085_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15;
    v___x_3086_ = l_Lean_stringToMessageData(v___x_3085_);
    return v___x_3086_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(
    mut v_mod_3091_: *mut LeanObject,
    mut v_isMeta_3092_: u8,
    mut v_hint_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3099_: u8 = 0;
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v_asyncMode_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3133_: u8 = 0;
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3143_: u8 = 0;
    let mut v_cls_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3097_ = lean_st_ref_get(v___y_3095_);
                v_env_3098_ = lean_ctor_get(v___x_3097_, 0);
                lean_inc_ref(v_env_3098_);
                lean_dec(v___x_3097_);
                v_isExporting_3099_ = lean_ctor_get_uint8(
                    v_env_3098_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_3098_);
                v___x_3100_ = lean_st_ref_get(v___y_3095_);
                v_env_3101_ = lean_ctor_get(v___x_3100_, 0);
                lean_inc_ref(v_env_3101_);
                lean_dec(v___x_3100_);
                v___x_3102_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2);
                lean_inc(v_mod_3091_);
                v_entry_3103_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_3103_, 0, v_mod_3091_);
                lean_ctor_set_uint8(
                    v_entry_3103_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_3099_,
                );
                lean_ctor_set_uint8(
                    v_entry_3103_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_3092_,
                );
                v___x_3104_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_3105_ = lean_box(1);
                v___x_3106_ = lean_box(0);
                v___x_3134_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3102_,
                    v___x_3104_,
                    v_env_3101_,
                    v___x_3105_,
                    v___x_3106_,
                );
                v___x_3135_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v___x_3134_, v_entry_3103_);
                lean_dec(v___x_3134_);
                if v___x_3135_ == 0 {
                    v___x_3136_ = l_Lean_inheritedTraceOptions;
                    v___x_3137_ = lean_st_ref_get(v___x_3136_);
                    v___x_3138_ = lean_st_ref_get(v___y_3095_);
                    v_scopes_3139_ = lean_ctor_get(v___x_3138_, 2);
                    lean_inc(v_scopes_3139_);
                    lean_dec(v___x_3138_);
                    v___x_3140_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3141_ = l_List_head_x21___redArg(v___x_3140_, v_scopes_3139_);
                    lean_dec(v_scopes_3139_);
                    v_opts_3142_ = lean_ctor_get(v___x_3141_, 1);
                    lean_inc_ref(v_opts_3142_);
                    lean_dec(v___x_3141_);
                    v_hasTrace_3143_ = lean_ctor_get_uint8(
                        v_opts_3142_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3143_ == 0 {
                        lean_dec_ref(v_opts_3142_);
                        lean_dec(v___x_3137_);
                        lean_dec(v_hint_3093_);
                        lean_dec(v_mod_3091_);
                        v___y_3108_ = v___y_3095_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_3144_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4;
                        v___x_3164_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12);
                        v___x_3165_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_3137_,
                            v_opts_3142_,
                            v___x_3164_,
                        );
                        lean_dec_ref(v_opts_3142_);
                        lean_dec(v___x_3137_);
                        if v___x_3165_ == 0 {
                            lean_dec(v_hint_3093_);
                            lean_dec(v_mod_3091_);
                            v___y_3108_ = v___y_3095_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3166_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14);
                            if v_isExporting_3099_ == 0 {
                                v___x_3175_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19;
                                v___y_3168_ = v___x_3175_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3176_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20;
                                v___y_3168_ = v___x_3176_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v_entry_3103_, 1);
                    lean_dec(v_hint_3093_);
                    lean_dec(v_mod_3091_);
                    v___x_3177_ = lean_box(0);
                    v___x_3178_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3178_, 0, v___x_3177_);
                    return v___x_3178_;
                }
            }
            1 => {
                v___x_3109_ = lean_st_ref_take(v___y_3108_);
                v_toEnvExtension_3110_ = lean_ctor_get(v___x_3104_, 0);
                v_env_3111_ = lean_ctor_get(v___x_3109_, 0);
                v_messages_3112_ = lean_ctor_get(v___x_3109_, 1);
                v_scopes_3113_ = lean_ctor_get(v___x_3109_, 2);
                v_usedQuotCtxts_3114_ = lean_ctor_get(v___x_3109_, 3);
                v_nextMacroScope_3115_ = lean_ctor_get(v___x_3109_, 4);
                v_maxRecDepth_3116_ = lean_ctor_get(v___x_3109_, 5);
                v_ngen_3117_ = lean_ctor_get(v___x_3109_, 6);
                v_auxDeclNGen_3118_ = lean_ctor_get(v___x_3109_, 7);
                v_infoState_3119_ = lean_ctor_get(v___x_3109_, 8);
                v_traceState_3120_ = lean_ctor_get(v___x_3109_, 9);
                v_snapshotTasks_3121_ = lean_ctor_get(v___x_3109_, 10);
                v_isSharedCheck_3133_ = (!lean_is_exclusive(v___x_3109_)) as u8;
                if v_isSharedCheck_3133_ == 0 {
                    v___x_3123_ = v___x_3109_;
                    v_isShared_3124_ = v_isSharedCheck_3133_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3121_);
                    lean_inc(v_traceState_3120_);
                    lean_inc(v_infoState_3119_);
                    lean_inc(v_auxDeclNGen_3118_);
                    lean_inc(v_ngen_3117_);
                    lean_inc(v_maxRecDepth_3116_);
                    lean_inc(v_nextMacroScope_3115_);
                    lean_inc(v_usedQuotCtxts_3114_);
                    lean_inc(v_scopes_3113_);
                    lean_inc(v_messages_3112_);
                    lean_inc(v_env_3111_);
                    lean_dec(v___x_3109_);
                    v___x_3123_ = lean_box(0);
                    v_isShared_3124_ = v_isSharedCheck_3133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_3125_ = lean_ctor_get(v_toEnvExtension_3110_, 2);
                v___x_3126_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3104_,
                    v_env_3111_,
                    v_entry_3103_,
                    v_asyncMode_3125_,
                    v___x_3106_,
                );
                if v_isShared_3124_ == 0 {
                    lean_ctor_set(v___x_3123_, 0, v___x_3126_);
                    v___x_3128_ = v___x_3123_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3126_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_messages_3112_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_scopes_3113_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_usedQuotCtxts_3114_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_nextMacroScope_3115_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 5, v_maxRecDepth_3116_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 6, v_ngen_3117_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 7, v_auxDeclNGen_3118_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 8, v_infoState_3119_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 9, v_traceState_3120_);
                    lean_ctor_set(v_reuseFailAlloc_3132_, 10, v_snapshotTasks_3121_);
                    v___x_3128_ = v_reuseFailAlloc_3132_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3129_ = lean_st_ref_set(v___y_3108_, v___x_3128_);
                v___x_3130_ = lean_box(0);
                v___x_3131_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3131_, 0, v___x_3130_);
                return v___x_3131_;
            }
            4 => {
                v___x_3148_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3148_, 0, v___y_3146_);
                lean_ctor_set(v___x_3148_, 1, v___y_3147_);
                v___x_3149_ =
                    l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(
                        v_cls_3144_,
                        v___x_3148_,
                        v___y_3094_,
                        v___y_3095_,
                    );
                if lean_obj_tag(v___x_3149_) == 0 {
                    lean_dec_ref_known(v___x_3149_, 1);
                    v___y_3108_ = v___y_3095_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_3103_, 1);
                    return v___x_3149_;
                }
            }
            5 => {
                lean_inc_ref(v___y_3152_);
                v___x_3153_ = l_Lean_stringToMessageData(v___y_3152_);
                v___x_3154_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3154_, 0, v___y_3151_);
                lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                v___x_3155_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6);
                v___x_3156_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3156_, 0, v___x_3154_);
                lean_ctor_set(v___x_3156_, 1, v___x_3155_);
                v___x_3157_ = l_Lean_MessageData_ofName(v_mod_3091_);
                v___x_3158_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3158_, 0, v___x_3156_);
                lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                v___x_3159_ = l_Lean_Name_isAnonymous(v_hint_3093_);
                if v___x_3159_ == 0 {
                    v___x_3160_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8);
                    v___x_3161_ = l_Lean_MessageData_ofName(v_hint_3093_);
                    v___x_3162_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3162_, 0, v___x_3160_);
                    lean_ctor_set(v___x_3162_, 1, v___x_3161_);
                    v___y_3146_ = v___x_3158_;
                    v___y_3147_ = v___x_3162_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_3093_);
                    v___x_3163_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9);
                    v___y_3146_ = v___x_3158_;
                    v___y_3147_ = v___x_3163_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_3168_);
                v___x_3169_ = l_Lean_stringToMessageData(v___y_3168_);
                v___x_3170_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3170_, 0, v___x_3166_);
                lean_ctor_set(v___x_3170_, 1, v___x_3169_);
                v___x_3171_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16);
                v___x_3172_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3172_, 0, v___x_3170_);
                lean_ctor_set(v___x_3172_, 1, v___x_3171_);
                if v_isMeta_3092_ == 0 {
                    v___x_3173_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17;
                    v___y_3151_ = v___x_3172_;
                    v___y_3152_ = v___x_3173_;
                    state = 5;
                    continue;
                } else {
                    v___x_3174_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18;
                    v___y_3151_ = v___x_3172_;
                    v___y_3152_ = v___x_3174_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(
    mut v_mod_3179_: *mut LeanObject,
    mut v_isMeta_3180_: *mut LeanObject,
    mut v_hint_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
    mut v___y_3183_: *mut LeanObject,
    mut v___y_3184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3185_: u8 = 0;
    let mut v_res_3186_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3185_ = (lean_unbox(v_isMeta_3180_) as u8);
    v_res_3186_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_mod_3179_, v_isMeta_boxed_3185_, v_hint_3181_, v___y_3182_, v___y_3183_);
    lean_dec(v___y_3183_);
    lean_dec_ref(v___y_3182_);
    return v_res_3186_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(
    mut v___x_3187_: *mut LeanObject,
    mut v_declName_3188_: *mut LeanObject,
    mut v_as_3189_: *mut LeanObject,
    mut v_sz_3190_: usize,
    mut v_i_3191_: usize,
    mut v_b_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3196_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: u8 = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3196_ = lean_usize_dec_lt(v_i_3191_, v_sz_3190_);
                if v___x_3196_ == 0 {
                    lean_dec(v_declName_3188_);
                    v___x_3197_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3197_, 0, v_b_3192_);
                    return v___x_3197_;
                } else {
                    v___x_3198_ = l_Lean_Environment_header(v___x_3187_);
                    v_modules_3199_ = lean_ctor_get(v___x_3198_, 3);
                    lean_inc_ref(v_modules_3199_);
                    lean_dec_ref(v___x_3198_);
                    v___x_3200_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_3201_ = lean_array_uget_borrowed(v_as_3189_, v_i_3191_);
                    v___x_3202_ = lean_array_get(v___x_3200_, v_modules_3199_, v_a_3201_);
                    lean_dec_ref(v_modules_3199_);
                    v_toImport_3203_ = lean_ctor_get(v___x_3202_, 0);
                    lean_inc_ref(v_toImport_3203_);
                    lean_dec(v___x_3202_);
                    v_module_3204_ = lean_ctor_get(v_toImport_3203_, 0);
                    lean_inc(v_module_3204_);
                    lean_dec_ref(v_toImport_3203_);
                    v___x_3205_ = 0;
                    lean_inc(v_declName_3188_);
                    v___x_3206_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_3204_, v___x_3205_, v_declName_3188_, v___y_3193_, v___y_3194_);
                    if lean_obj_tag(v___x_3206_) == 0 {
                        lean_dec_ref_known(v___x_3206_, 1);
                        v___x_3207_ = lean_box(0);
                        v___x_3208_ = 1usize;
                        v___x_3209_ = lean_usize_add(v_i_3191_, v___x_3208_);
                        v_i_3191_ = v___x_3209_;
                        v_b_3192_ = v___x_3207_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_3188_);
                        return v___x_3206_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(
    mut v___x_3211_: *mut LeanObject,
    mut v_declName_3212_: *mut LeanObject,
    mut v_as_3213_: *mut LeanObject,
    mut v_sz_3214_: *mut LeanObject,
    mut v_i_3215_: *mut LeanObject,
    mut v_b_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3220_: usize = 0;
    let mut v_i_boxed_3221_: usize = 0;
    let mut v_res_3222_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3220_ = lean_unbox_usize(v_sz_3214_);
    lean_dec(v_sz_3214_);
    v_i_boxed_3221_ = lean_unbox_usize(v_i_3215_);
    lean_dec(v_i_3215_);
    v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v___x_3211_, v_declName_3212_, v_as_3213_, v_sz_boxed_3220_, v_i_boxed_3221_, v_b_3216_, v___y_3217_, v___y_3218_);
    lean_dec(v___y_3218_);
    lean_dec_ref(v___y_3217_);
    lean_dec_ref(v_as_3213_);
    lean_dec_ref(v___x_3211_);
    return v_res_3222_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(
    mut v_a_3223_: *mut LeanObject,
    mut v_x_3224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3224_) == 0 {
                    v___x_3225_ = lean_box(0);
                    return v___x_3225_;
                } else {
                    v_key_3226_ = lean_ctor_get(v_x_3224_, 0);
                    v_value_3227_ = lean_ctor_get(v_x_3224_, 1);
                    v_tail_3228_ = lean_ctor_get(v_x_3224_, 2);
                    v___x_3229_ = lean_name_eq(v_key_3226_, v_a_3223_);
                    if v___x_3229_ == 0 {
                        v_x_3224_ = v_tail_3228_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3227_);
                        v___x_3231_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3231_, 0, v_value_3227_);
                        return v___x_3231_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(
    mut v_a_3232_: *mut LeanObject,
    mut v_x_3233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3234_: *mut LeanObject = core::ptr::null_mut();
    v_res_3234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_3232_, v_x_3233_);
    lean_dec(v_x_3233_);
    lean_dec(v_a_3232_);
    return v_res_3234_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u64 = 0;
    v___x_3235_ = lean_unsigned_to_nat(1723);
    v___x_3236_ = lean_uint64_of_nat(v___x_3235_);
    return v___x_3236_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(
    mut v_m_3237_: *mut LeanObject,
    mut v_a_3238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3242_: u64 = 0;
    let mut v___x_3243_: u64 = 0;
    let mut v___x_3244_: u64 = 0;
    let mut v_fold_3245_: u64 = 0;
    let mut v___x_3246_: u64 = 0;
    let mut v___x_3247_: u64 = 0;
    let mut v___x_3248_: u64 = 0;
    let mut v___x_3249_: usize = 0;
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v___x_3253_: usize = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u64 = 0;
    let mut v_hash_3257_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3239_ = lean_ctor_get(v_m_3237_, 1);
                v___x_3240_ = lean_array_get_size(v_buckets_3239_);
                if lean_obj_tag(v_a_3238_) == 0 {
                    v___x_3256_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0);
                    v___y_3242_ = v___x_3256_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3257_ = lean_ctor_get_uint64(
                        v_a_3238_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3242_ = v_hash_3257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3243_ = 32u64;
                v___x_3244_ = lean_uint64_shift_right(v___y_3242_, v___x_3243_);
                v_fold_3245_ = lean_uint64_xor(v___y_3242_, v___x_3244_);
                v___x_3246_ = 16u64;
                v___x_3247_ = lean_uint64_shift_right(v_fold_3245_, v___x_3246_);
                v___x_3248_ = lean_uint64_xor(v_fold_3245_, v___x_3247_);
                v___x_3249_ = lean_uint64_to_usize(v___x_3248_);
                v___x_3250_ = lean_usize_of_nat(v___x_3240_);
                v___x_3251_ = 1usize;
                v___x_3252_ = lean_usize_sub(v___x_3250_, v___x_3251_);
                v___x_3253_ = lean_usize_land(v___x_3249_, v___x_3252_);
                v___x_3254_ = lean_array_uget_borrowed(v_buckets_3239_, v___x_3253_);
                v___x_3255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_3238_, v___x_3254_);
                return v___x_3255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_m_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3260_: *mut LeanObject = core::ptr::null_mut();
    v_res_3260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_3258_, v_a_3259_);
    lean_dec(v_a_3259_);
    lean_dec_ref(v_m_3258_);
    return v_res_3260_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1;
    v___x_3264_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0;
    v___x_3265_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3264_, v___x_3263_);
    return v___x_3265_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(
    mut v_declName_3268_: *mut LeanObject,
    mut v_isMeta_3269_: u8,
    mut v___y_3270_: *mut LeanObject,
    mut v___y_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3281_: usize = 0;
    let mut v___x_3282_: usize = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_unused_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: u8 = 0;
    let mut v_toImport_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3273_ = lean_st_ref_get(v___y_3271_);
                v_env_3277_ = lean_ctor_get(v___x_3273_, 0);
                lean_inc_ref(v_env_3277_);
                lean_dec(v___x_3273_);
                v___x_3292_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3277_, v_declName_3268_);
                if lean_obj_tag(v___x_3292_) == 0 {
                    lean_dec_ref(v_env_3277_);
                    lean_dec(v_declName_3268_);
                    state = 1;
                    continue;
                } else {
                    v_val_3293_ = lean_ctor_get(v___x_3292_, 0);
                    lean_inc(v_val_3293_);
                    lean_dec_ref_known(v___x_3292_, 1);
                    v___x_3294_ = l_Lean_Environment_header(v_env_3277_);
                    v_modules_3295_ = lean_ctor_get(v___x_3294_, 3);
                    lean_inc_ref(v_modules_3295_);
                    lean_dec_ref(v___x_3294_);
                    v___x_3296_ = lean_array_get_size(v_modules_3295_);
                    v___x_3297_ = lean_nat_dec_lt(v_val_3293_, v___x_3296_);
                    if v___x_3297_ == 0 {
                        lean_dec_ref(v_modules_3295_);
                        lean_dec(v_val_3293_);
                        lean_dec_ref(v_env_3277_);
                        lean_dec(v_declName_3268_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3298_ = lean_st_ref_get(v___y_3271_);
                        v_env_3299_ = lean_ctor_get(v___x_3298_, 0);
                        lean_inc_ref(v_env_3299_);
                        lean_dec(v___x_3298_);
                        v___x_3300_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2);
                        v___x_3301_ = lean_array_fget(v_modules_3295_, v_val_3293_);
                        lean_dec(v_val_3293_);
                        lean_dec_ref(v_modules_3295_);
                        if v_isMeta_3269_ == 0 {
                            lean_dec_ref(v_env_3299_);
                            v___y_3303_ = v_isMeta_3269_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_3268_);
                            v___x_3314_ = l_Lean_isMarkedMeta(v_env_3299_, v_declName_3268_);
                            if v___x_3314_ == 0 {
                                v___y_3303_ = v_isMeta_3269_;
                                state = 5;
                                continue;
                            } else {
                                v___x_3315_ = 0;
                                v___y_3303_ = v___x_3315_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3275_ = lean_box(0);
                v___x_3276_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                return v___x_3276_;
            }
            2 => {
                v___x_3280_ = lean_box(0);
                v_sz_3281_ = lean_array_size(v___y_3279_);
                v___x_3282_ = 0usize;
                v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_env_3277_, v_declName_3268_, v___y_3279_, v_sz_3281_, v___x_3282_, v___x_3280_, v___y_3270_, v___y_3271_);
                lean_dec_ref(v___y_3279_);
                lean_dec_ref(v_env_3277_);
                if lean_obj_tag(v___x_3283_) == 0 {
                    v_isSharedCheck_3290_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                    if v_isSharedCheck_3290_ == 0 {
                        v_unused_3291_ = lean_ctor_get(v___x_3283_, 0);
                        lean_dec(v_unused_3291_);
                        v___x_3285_ = v___x_3283_;
                        v_isShared_3286_ = v_isSharedCheck_3290_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_3283_);
                        v___x_3285_ = lean_box(0);
                        v_isShared_3286_ = v_isSharedCheck_3290_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_3283_;
                }
            }
            3 => {
                if v_isShared_3286_ == 0 {
                    lean_ctor_set(v___x_3285_, 0, v___x_3280_);
                    v___x_3288_ = v___x_3285_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3280_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3288_;
            }
            5 => {
                v_toImport_3304_ = lean_ctor_get(v___x_3301_, 0);
                lean_inc_ref(v_toImport_3304_);
                lean_dec(v___x_3301_);
                v_module_3305_ = lean_ctor_get(v_toImport_3304_, 0);
                lean_inc(v_module_3305_);
                lean_dec_ref(v_toImport_3304_);
                lean_inc(v_declName_3268_);
                v___x_3306_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_3305_, v___y_3303_, v_declName_3268_, v___y_3270_, v___y_3271_);
                if lean_obj_tag(v___x_3306_) == 0 {
                    lean_dec_ref_known(v___x_3306_, 1);
                    v___x_3307_ = l_Lean_indirectModUseExt;
                    v___x_3308_ = lean_box(1);
                    v___x_3309_ = lean_box(0);
                    lean_inc_ref(v_env_3277_);
                    v___x_3310_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_3300_,
                        v___x_3307_,
                        v_env_3277_,
                        v___x_3308_,
                        v___x_3309_,
                    );
                    v___x_3311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v___x_3310_, v_declName_3268_);
                    lean_dec(v___x_3310_);
                    if lean_obj_tag(v___x_3311_) == 0 {
                        v___x_3312_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3;
                        v___y_3279_ = v___x_3312_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3313_ = lean_ctor_get(v___x_3311_, 0);
                        lean_inc(v_val_3313_);
                        lean_dec_ref_known(v___x_3311_, 1);
                        v___y_3279_ = v_val_3313_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_3277_);
                    lean_dec(v_declName_3268_);
                    return v___x_3306_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(
    mut v_declName_3316_: *mut LeanObject,
    mut v_isMeta_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3321_: u8 = 0;
    let mut v_res_3322_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3321_ = (lean_unbox(v_isMeta_3317_) as u8);
    v_res_3322_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_declName_3316_, v_isMeta_boxed_3321_, v___y_3318_, v___y_3319_);
    lean_dec(v___y_3319_);
    lean_dec_ref(v___y_3318_);
    return v_res_3322_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(
    mut v_as_x27_3323_: *mut LeanObject,
    mut v_b_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3323_) == 0 {
                    v___x_3328_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3328_, 0, v_b_3324_);
                    return v___x_3328_;
                } else {
                    v_head_3329_ = lean_ctor_get(v_as_x27_3323_, 0);
                    v_tail_3330_ = lean_ctor_get(v_as_x27_3323_, 1);
                    v___x_3331_ = 1;
                    lean_inc(v_head_3329_);
                    v___x_3332_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_head_3329_, v___x_3331_, v___y_3325_, v___y_3326_);
                    if lean_obj_tag(v___x_3332_) == 0 {
                        lean_dec_ref_known(v___x_3332_, 1);
                        v___x_3333_ = lean_box(0);
                        v_as_x27_3323_ = v_tail_3330_;
                        v_b_3324_ = v___x_3333_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3332_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(
    mut v_as_x27_3335_: *mut LeanObject,
    mut v_b_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3340_: *mut LeanObject = core::ptr::null_mut();
    v_res_3340_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_3335_, v_b_3336_, v___y_3337_, v___y_3338_);
    lean_dec(v___y_3338_);
    lean_dec_ref(v___y_3337_);
    lean_dec(v_as_x27_3335_);
    return v_res_3340_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(
    mut v_opts_3341_: *mut LeanObject,
    mut v_opt_3342_: *mut LeanObject,
) -> u8 {
    let mut v_name_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v_name_3343_ = lean_ctor_get(v_opt_3342_, 0);
    v_defValue_3344_ = lean_ctor_get(v_opt_3342_, 1);
    v_map_3345_ = lean_ctor_get(v_opts_3341_, 0);
    v___x_3346_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3345_,
            v_name_3343_,
        );
    if lean_obj_tag(v___x_3346_) == 0 {
        let mut v___x_3347_: u8 = 0;
        v___x_3347_ = (lean_unbox(v_defValue_3344_) as u8);
        return v___x_3347_;
    } else {
        let mut v_val_3348_: *mut LeanObject = core::ptr::null_mut();
        v_val_3348_ = lean_ctor_get(v___x_3346_, 0);
        lean_inc(v_val_3348_);
        lean_dec_ref_known(v___x_3346_, 1);
        if lean_obj_tag(v_val_3348_) == 1 {
            let mut v_v_3349_: u8 = 0;
            v_v_3349_ = lean_ctor_get_uint8(v_val_3348_, 0 as u32);
            lean_dec_ref_known(v_val_3348_, 0);
            return v_v_3349_;
        } else {
            let mut v___x_3350_: u8 = 0;
            lean_dec(v_val_3348_);
            v___x_3350_ = (lean_unbox(v_defValue_3344_) as u8);
            return v___x_3350_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18___boxed(
    mut v_opts_3351_: *mut LeanObject,
    mut v_opt_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3353_: u8 = 0;
    let mut v_r_3354_: *mut LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_3351_, v_opt_3352_);
    lean_dec_ref(v_opt_3352_);
    lean_dec_ref(v_opts_3351_);
    v_r_3354_ = lean_box((v_res_3353_) as usize);
    return v_r_3354_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0()
-> *mut LeanObject {
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    v___x_3355_ = lean_box(1);
    v___x_3356_ = l_Lean_MessageData_ofFormat(v___x_3355_);
    return v___x_3356_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3()
-> *mut LeanObject {
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    v___x_3360_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2;
    v___x_3361_ = l_Lean_MessageData_ofFormat(v___x_3360_);
    return v___x_3361_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(
    mut v_x_3362_: *mut LeanObject,
    mut v_x_3363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v_before_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3385_: u8 = 0;
    let mut v_unused_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3363_) == 0 {
                    return v_x_3362_;
                } else {
                    v_head_3364_ = lean_ctor_get(v_x_3363_, 0);
                    v_tail_3365_ = lean_ctor_get(v_x_3363_, 1);
                    v_isSharedCheck_3387_ = (!lean_is_exclusive(v_x_3363_)) as u8;
                    if v_isSharedCheck_3387_ == 0 {
                        v___x_3367_ = v_x_3363_;
                        v_isShared_3368_ = v_isSharedCheck_3387_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3365_);
                        lean_inc(v_head_3364_);
                        lean_dec(v_x_3363_);
                        v___x_3367_ = lean_box(0);
                        v_isShared_3368_ = v_isSharedCheck_3387_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3369_ = lean_ctor_get(v_head_3364_, 0);
                v_isSharedCheck_3385_ = (!lean_is_exclusive(v_head_3364_)) as u8;
                if v_isSharedCheck_3385_ == 0 {
                    v_unused_3386_ = lean_ctor_get(v_head_3364_, 1);
                    lean_dec(v_unused_3386_);
                    v___x_3371_ = v_head_3364_;
                    v_isShared_3372_ = v_isSharedCheck_3385_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_3369_);
                    lean_dec(v_head_3364_);
                    v___x_3371_ = lean_box(0);
                    v_isShared_3372_ = v_isSharedCheck_3385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3373_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
                if v_isShared_3372_ == 0 {
                    lean_ctor_set_tag(v___x_3371_, 7);
                    lean_ctor_set(v___x_3371_, 1, v___x_3373_);
                    lean_ctor_set(v___x_3371_, 0, v_x_3362_);
                    v___x_3375_ = v___x_3371_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3384_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_x_3362_);
                    lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3373_);
                    v___x_3375_ = v_reuseFailAlloc_3384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3376_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3);
                if v_isShared_3368_ == 0 {
                    lean_ctor_set_tag(v___x_3367_, 7);
                    lean_ctor_set(v___x_3367_, 1, v___x_3376_);
                    lean_ctor_set(v___x_3367_, 0, v___x_3375_);
                    v___x_3378_ = v___x_3367_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3375_);
                    lean_ctor_set(v_reuseFailAlloc_3383_, 1, v___x_3376_);
                    v___x_3378_ = v_reuseFailAlloc_3383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3379_ = l_Lean_MessageData_ofSyntax(v_before_3369_);
                v___x_3380_ = l_Lean_indentD(v___x_3379_);
                v___x_3381_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3381_, 0, v___x_3378_);
                lean_ctor_set(v___x_3381_, 1, v___x_3380_);
                v_x_3362_ = v___x_3381_;
                v_x_3363_ = v_tail_3365_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    v___x_3391_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1;
    v___x_3392_ = l_Lean_MessageData_ofFormat(v___x_3391_);
    return v___x_3392_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(
    mut v_msgData_3393_: *mut LeanObject,
    mut v_macroStack_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3422_: u8 = 0;
    let mut v_unused_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3397_ = lean_st_ref_get(v___y_3395_);
                v_scopes_3398_ = lean_ctor_get(v___x_3397_, 2);
                lean_inc(v_scopes_3398_);
                lean_dec(v___x_3397_);
                v___x_3399_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3400_ = l_List_head_x21___redArg(v___x_3399_, v_scopes_3398_);
                lean_dec(v_scopes_3398_);
                v_opts_3401_ = lean_ctor_get(v___x_3400_, 1);
                lean_inc_ref(v_opts_3401_);
                lean_dec(v___x_3400_);
                v___x_3402_ = l_Lean_Elab_pp_macroStack;
                v___x_3403_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_3401_, v___x_3402_);
                lean_dec_ref(v_opts_3401_);
                if v___x_3403_ == 0 {
                    lean_dec(v_macroStack_3394_);
                    v___x_3404_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3404_, 0, v_msgData_3393_);
                    return v___x_3404_;
                } else {
                    if lean_obj_tag(v_macroStack_3394_) == 0 {
                        v___x_3405_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3405_, 0, v_msgData_3393_);
                        return v___x_3405_;
                    } else {
                        v_head_3406_ = lean_ctor_get(v_macroStack_3394_, 0);
                        lean_inc(v_head_3406_);
                        v_after_3407_ = lean_ctor_get(v_head_3406_, 1);
                        v_isSharedCheck_3422_ = (!lean_is_exclusive(v_head_3406_)) as u8;
                        if v_isSharedCheck_3422_ == 0 {
                            v_unused_3423_ = lean_ctor_get(v_head_3406_, 0);
                            lean_dec(v_unused_3423_);
                            v___x_3409_ = v_head_3406_;
                            v_isShared_3410_ = v_isSharedCheck_3422_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_3407_);
                            lean_dec(v_head_3406_);
                            v___x_3409_ = lean_box(0);
                            v_isShared_3410_ = v_isSharedCheck_3422_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3411_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
                if v_isShared_3410_ == 0 {
                    lean_ctor_set_tag(v___x_3409_, 7);
                    lean_ctor_set(v___x_3409_, 1, v___x_3411_);
                    lean_ctor_set(v___x_3409_, 0, v_msgData_3393_);
                    v___x_3413_ = v___x_3409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_msgData_3393_);
                    lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3411_);
                    v___x_3413_ = v_reuseFailAlloc_3421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3414_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2);
                v___x_3415_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3415_, 0, v___x_3413_);
                lean_ctor_set(v___x_3415_, 1, v___x_3414_);
                v___x_3416_ = l_Lean_MessageData_ofSyntax(v_after_3407_);
                v___x_3417_ = l_Lean_indentD(v___x_3416_);
                v_msgData_3418_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_3418_, 0, v___x_3415_);
                lean_ctor_set(v_msgData_3418_, 1, v___x_3417_);
                v___x_3419_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(v_msgData_3418_, v_macroStack_3394_);
                v___x_3420_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3420_, 0, v___x_3419_);
                return v___x_3420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___boxed(
    mut v_msgData_3424_: *mut LeanObject,
    mut v_macroStack_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
    mut v___y_3427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3428_: *mut LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_3424_, v_macroStack_3425_, v___y_3426_);
    lean_dec(v___y_3426_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(
    mut v_msg_3429_: *mut LeanObject,
    mut v___y_3430_: *mut LeanObject,
    mut v___y_3431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v_a_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3433_ = l_Lean_Elab_Command_getRef___redArg(v___y_3430_);
                if lean_obj_tag(v___x_3433_) == 0 {
                    v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
                    lean_inc(v_a_3434_);
                    lean_dec_ref_known(v___x_3433_, 1);
                    v_macroStack_3435_ = lean_ctor_get(v___y_3430_, 4);
                    v___x_3436_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_3429_, v___y_3431_);
                    v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
                    lean_inc(v_a_3437_);
                    lean_dec_ref(v___x_3436_);
                    v___x_3438_ = l_Lean_Elab_getBetterRef(v_a_3434_, v_macroStack_3435_);
                    lean_dec(v_a_3434_);
                    lean_inc(v_macroStack_3435_);
                    v___x_3439_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_a_3437_, v_macroStack_3435_, v___y_3431_);
                    v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
                    v_isSharedCheck_3448_ = (!lean_is_exclusive(v___x_3439_)) as u8;
                    if v_isSharedCheck_3448_ == 0 {
                        v___x_3442_ = v___x_3439_;
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3440_);
                        lean_dec(v___x_3439_);
                        v___x_3442_ = lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_3429_);
                    v_a_3449_ = lean_ctor_get(v___x_3433_, 0);
                    v_isSharedCheck_3456_ = (!lean_is_exclusive(v___x_3433_)) as u8;
                    if v_isSharedCheck_3456_ == 0 {
                        v___x_3451_ = v___x_3433_;
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3449_);
                        lean_dec(v___x_3433_);
                        v___x_3451_ = lean_box(0);
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3444_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3444_, 0, v___x_3438_);
                lean_ctor_set(v___x_3444_, 1, v_a_3440_);
                if v_isShared_3443_ == 0 {
                    lean_ctor_set_tag(v___x_3442_, 1);
                    lean_ctor_set(v___x_3442_, 0, v___x_3444_);
                    v___x_3446_ = v___x_3442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
                    v___x_3446_ = v_reuseFailAlloc_3447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3446_;
            }
            3 => {
                if v_isShared_3452_ == 0 {
                    v___x_3454_ = v___x_3451_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
                    v___x_3454_ = v_reuseFailAlloc_3455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg___boxed(
    mut v_msg_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3461_: *mut LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_3457_, v___y_3458_, v___y_3459_);
    lean_dec(v___y_3459_);
    lean_dec_ref(v___y_3458_);
    return v_res_3461_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(
    mut v_ref_3462_: *mut LeanObject,
    mut v_msg_3463_: *mut LeanObject,
    mut v___y_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3478_: u8 = 0;
    let mut v_ref_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3467_ = l_Lean_Elab_Command_getRef___redArg(v___y_3464_);
                if lean_obj_tag(v___x_3467_) == 0 {
                    v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
                    lean_inc(v_a_3468_);
                    lean_dec_ref_known(v___x_3467_, 1);
                    v_fileName_3469_ = lean_ctor_get(v___y_3464_, 0);
                    v_fileMap_3470_ = lean_ctor_get(v___y_3464_, 1);
                    v_currRecDepth_3471_ = lean_ctor_get(v___y_3464_, 2);
                    v_cmdPos_3472_ = lean_ctor_get(v___y_3464_, 3);
                    v_macroStack_3473_ = lean_ctor_get(v___y_3464_, 4);
                    v_quotContext_x3f_3474_ = lean_ctor_get(v___y_3464_, 5);
                    v_currMacroScope_3475_ = lean_ctor_get(v___y_3464_, 6);
                    v_snap_x3f_3476_ = lean_ctor_get(v___y_3464_, 8);
                    v_cancelTk_x3f_3477_ = lean_ctor_get(v___y_3464_, 9);
                    v_suppressElabErrors_3478_ = lean_ctor_get_uint8(
                        v___y_3464_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_3479_ = l_Lean_replaceRef(v_ref_3462_, v_a_3468_);
                    lean_dec(v_a_3468_);
                    lean_inc(v_cancelTk_x3f_3477_);
                    lean_inc(v_snap_x3f_3476_);
                    lean_inc(v_currMacroScope_3475_);
                    lean_inc(v_quotContext_x3f_3474_);
                    lean_inc(v_macroStack_3473_);
                    lean_inc(v_cmdPos_3472_);
                    lean_inc(v_currRecDepth_3471_);
                    lean_inc_ref(v_fileMap_3470_);
                    lean_inc_ref(v_fileName_3469_);
                    v___x_3480_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_3480_, 0, v_fileName_3469_);
                    lean_ctor_set(v___x_3480_, 1, v_fileMap_3470_);
                    lean_ctor_set(v___x_3480_, 2, v_currRecDepth_3471_);
                    lean_ctor_set(v___x_3480_, 3, v_cmdPos_3472_);
                    lean_ctor_set(v___x_3480_, 4, v_macroStack_3473_);
                    lean_ctor_set(v___x_3480_, 5, v_quotContext_x3f_3474_);
                    lean_ctor_set(v___x_3480_, 6, v_currMacroScope_3475_);
                    lean_ctor_set(v___x_3480_, 7, v_ref_3479_);
                    lean_ctor_set(v___x_3480_, 8, v_snap_x3f_3476_);
                    lean_ctor_set(v___x_3480_, 9, v_cancelTk_x3f_3477_);
                    lean_ctor_set_uint8(
                        v___x_3480_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_3478_,
                    );
                    v___x_3481_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_3463_, v___x_3480_, v___y_3465_);
                    lean_dec_ref_known(v___x_3480_, 10);
                    return v___x_3481_;
                } else {
                    lean_dec_ref(v_msg_3463_);
                    v_a_3482_ = lean_ctor_get(v___x_3467_, 0);
                    v_isSharedCheck_3489_ = (!lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3489_ == 0 {
                        v___x_3484_ = v___x_3467_;
                        v_isShared_3485_ = v_isSharedCheck_3489_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3482_);
                        lean_dec(v___x_3467_);
                        v___x_3484_ = lean_box(0);
                        v_isShared_3485_ = v_isSharedCheck_3489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3485_ == 0 {
                    v___x_3487_ = v___x_3484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(
    mut v_ref_3490_: *mut LeanObject,
    mut v_msg_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3495_: *mut LeanObject = core::ptr::null_mut();
    v_res_3495_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_3490_, v_msg_3491_, v___y_3492_, v___y_3493_);
    lean_dec(v___y_3493_);
    lean_dec_ref(v___y_3492_);
    lean_dec(v_ref_3490_);
    return v_res_3495_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(
    mut v_env_3496_: *mut LeanObject,
    mut v_declName_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
    mut v___y_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3500_: u8 = 0;
    let mut v_env_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: u8 = 0;
    v___x_3500_ = 0;
    v_env_3501_ = l_Lean_Environment_setExporting(v_env_3496_, v___x_3500_);
    lean_inc(v_declName_3497_);
    v___x_3502_ = l_Lean_mkPrivateName(v_env_3501_, v_declName_3497_);
    v___x_3503_ = 1;
    lean_inc_ref(v_env_3501_);
    v___x_3504_ = l_Lean_Environment_contains(v_env_3501_, v___x_3502_, v___x_3503_);
    if v___x_3504_ == 0 {
        let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3506_: u8 = 0;
        let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
        v___x_3505_ = l_Lean_privateToUserName(v_declName_3497_);
        v___x_3506_ = l_Lean_Environment_contains(v_env_3501_, v___x_3505_, v___x_3503_);
        v___x_3507_ = lean_box((v___x_3506_) as usize);
        v___x_3508_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3508_, 0, v___x_3507_);
        lean_ctor_set(v___x_3508_, 1, v___y_3499_);
        return v___x_3508_;
    } else {
        let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_3501_);
        lean_dec(v_declName_3497_);
        v___x_3509_ = lean_box((v___x_3504_) as usize);
        v___x_3510_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3510_, 0, v___x_3509_);
        lean_ctor_set(v___x_3510_, 1, v___y_3499_);
        return v___x_3510_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(
    mut v_env_3511_: *mut LeanObject,
    mut v_declName_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3515_: *mut LeanObject = core::ptr::null_mut();
    v_res_3515_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(v_env_3511_, v_declName_3512_, v___y_3513_, v___y_3514_);
    lean_dec_ref(v___y_3513_);
    return v_res_3515_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(
    mut v_as_3516_: *mut LeanObject,
    mut v___y_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3533_: u8 = 0;
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_3516_) == 0 {
                    v___x_3520_ = lean_box(0);
                    v___x_3521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3521_, 0, v___x_3520_);
                    return v___x_3521_;
                } else {
                    v_head_3522_ = lean_ctor_get(v_as_3516_, 0);
                    lean_inc(v_head_3522_);
                    v_tail_3523_ = lean_ctor_get(v_as_3516_, 1);
                    lean_inc(v_tail_3523_);
                    lean_dec_ref_known(v_as_3516_, 2);
                    v_fst_3524_ = lean_ctor_get(v_head_3522_, 0);
                    lean_inc(v_fst_3524_);
                    v_snd_3525_ = lean_ctor_get(v_head_3522_, 1);
                    lean_inc(v_snd_3525_);
                    lean_dec(v_head_3522_);
                    v___x_3526_ = l_Lean_inheritedTraceOptions;
                    v___x_3527_ = lean_st_ref_get(v___x_3526_);
                    v___x_3528_ = lean_st_ref_get(v___y_3518_);
                    v_scopes_3529_ = lean_ctor_get(v___x_3528_, 2);
                    lean_inc(v_scopes_3529_);
                    lean_dec(v___x_3528_);
                    v___x_3530_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3531_ = l_List_head_x21___redArg(v___x_3530_, v_scopes_3529_);
                    lean_dec(v_scopes_3529_);
                    v_opts_3532_ = lean_ctor_get(v___x_3531_, 1);
                    lean_inc_ref(v_opts_3532_);
                    lean_dec(v___x_3531_);
                    v_hasTrace_3533_ = lean_ctor_get_uint8(
                        v_opts_3532_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3533_ == 0 {
                        lean_dec_ref(v_opts_3532_);
                        lean_dec(v___x_3527_);
                        lean_dec(v_snd_3525_);
                        lean_dec(v_fst_3524_);
                        v_as_3516_ = v_tail_3523_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3535_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11;
                        lean_inc(v_fst_3524_);
                        v___x_3536_ = l_Lean_Name_append(v___x_3535_, v_fst_3524_);
                        v___x_3537_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_3527_,
                            v_opts_3532_,
                            v___x_3536_,
                        );
                        lean_dec(v___x_3536_);
                        lean_dec_ref(v_opts_3532_);
                        lean_dec(v___x_3527_);
                        if v___x_3537_ == 0 {
                            lean_dec(v_snd_3525_);
                            lean_dec(v_fst_3524_);
                            v_as_3516_ = v_tail_3523_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3539_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_3539_, 0, v_snd_3525_);
                            v___x_3540_ = l_Lean_MessageData_ofFormat(v___x_3539_);
                            v___x_3541_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_fst_3524_, v___x_3540_, v___y_3517_, v___y_3518_);
                            if lean_obj_tag(v___x_3541_) == 0 {
                                lean_dec_ref_known(v___x_3541_, 1);
                                v_as_3516_ = v_tail_3523_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_tail_3523_);
                                return v___x_3541_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(
    mut v_as_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3547_: *mut LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v_as_3543_, v___y_3544_, v___y_3545_);
    lean_dec(v___y_3545_);
    lean_dec_ref(v___y_3544_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(
    mut v_env_3548_: *mut LeanObject,
    mut v_opts_3549_: *mut LeanObject,
    mut v_currNamespace_3550_: *mut LeanObject,
    mut v_openDecls_3551_: *mut LeanObject,
    mut v_n_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_3548_,
        v_opts_3549_,
        v_currNamespace_3550_,
        v_openDecls_3551_,
        v_n_3552_,
    );
    v___x_3556_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3556_, 0, v___x_3555_);
    lean_ctor_set(v___x_3556_, 1, v___y_3554_);
    return v___x_3556_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(
    mut v_env_3557_: *mut LeanObject,
    mut v_opts_3558_: *mut LeanObject,
    mut v_currNamespace_3559_: *mut LeanObject,
    mut v_openDecls_3560_: *mut LeanObject,
    mut v_n_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3564_: *mut LeanObject = core::ptr::null_mut();
    v_res_3564_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(v_env_3557_, v_opts_3558_, v_currNamespace_3559_, v_openDecls_3560_, v_n_3561_, v___y_3562_, v___y_3563_);
    lean_dec_ref(v___y_3562_);
    lean_dec_ref(v_opts_3558_);
    return v_res_3564_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(
    mut v_x_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroScope_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3625_: u8 = 0;
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut v_unused_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_reuseFailAlloc_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_unused_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3657_: u8 = 0;
    let mut v_a_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3674_: u8 = 0;
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_a_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3682_: u8 = 0;
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_a_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_a_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3570_ = lean_st_ref_get(v___y_3568_);
                v_env_3571_ = lean_ctor_get(v___x_3570_, 0);
                lean_inc_ref(v_env_3571_);
                lean_dec(v___x_3570_);
                v___x_3572_ = lean_st_ref_get(v___y_3568_);
                v_scopes_3573_ = lean_ctor_get(v___x_3572_, 2);
                lean_inc(v_scopes_3573_);
                lean_dec(v___x_3572_);
                v___x_3574_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3575_ = l_List_head_x21___redArg(v___x_3574_, v_scopes_3573_);
                lean_dec(v_scopes_3573_);
                v_opts_3576_ = lean_ctor_get(v___x_3575_, 1);
                lean_inc_ref(v_opts_3576_);
                lean_dec(v___x_3575_);
                v___x_3577_ = l_Lean_Elab_Command_getScope___redArg(v___y_3568_);
                if lean_obj_tag(v___x_3577_) == 0 {
                    v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
                    lean_inc(v_a_3578_);
                    lean_dec_ref_known(v___x_3577_, 1);
                    v_currNamespace_3579_ = lean_ctor_get(v_a_3578_, 2);
                    lean_inc(v_currNamespace_3579_);
                    lean_dec(v_a_3578_);
                    v___x_3580_ = l_Lean_Elab_Command_getScope___redArg(v___y_3568_);
                    if lean_obj_tag(v___x_3580_) == 0 {
                        v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
                        lean_inc(v_a_3581_);
                        lean_dec_ref_known(v___x_3580_, 1);
                        v_openDecls_3582_ = lean_ctor_get(v_a_3581_, 3);
                        lean_inc(v_openDecls_3582_);
                        lean_dec(v_a_3581_);
                        v___x_3583_ = l_Lean_Elab_Command_getRef___redArg(v___y_3567_);
                        if lean_obj_tag(v___x_3583_) == 0 {
                            v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
                            lean_inc(v_a_3584_);
                            lean_dec_ref_known(v___x_3583_, 1);
                            v___x_3585_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3567_);
                            if lean_obj_tag(v___x_3585_) == 0 {
                                v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
                                lean_inc(v_a_3586_);
                                lean_dec_ref_known(v___x_3585_, 1);
                                v_currRecDepth_3587_ = lean_ctor_get(v___y_3567_, 2);
                                v_quotContext_x3f_3588_ = lean_ctor_get(v___y_3567_, 5);
                                lean_inc_ref_n(v_env_3571_, 3);
                                v___f_3589_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                                lean_closure_set(v___f_3589_, 0, v_env_3571_);
                                v___f_3590_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                                lean_closure_set(v___f_3590_, 0, v_env_3571_);
                                lean_inc_n(v_currNamespace_3579_, 2);
                                v___f_3591_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                                lean_closure_set(v___f_3591_, 0, v_currNamespace_3579_);
                                lean_inc(v_openDecls_3582_);
                                v___f_3592_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                                lean_closure_set(v___f_3592_, 0, v_env_3571_);
                                lean_closure_set(v___f_3592_, 1, v_currNamespace_3579_);
                                lean_closure_set(v___f_3592_, 2, v_openDecls_3582_);
                                v___f_3593_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                                lean_closure_set(v___f_3593_, 0, v_env_3571_);
                                lean_closure_set(v___f_3593_, 1, v_opts_3576_);
                                lean_closure_set(v___f_3593_, 2, v_currNamespace_3579_);
                                lean_closure_set(v___f_3593_, 3, v_openDecls_3582_);
                                v_methods_3594_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_methods_3594_, 0, v___f_3590_);
                                lean_ctor_set(v_methods_3594_, 1, v___f_3591_);
                                lean_ctor_set(v_methods_3594_, 2, v___f_3589_);
                                lean_ctor_set(v_methods_3594_, 3, v___f_3592_);
                                lean_ctor_set(v_methods_3594_, 4, v___f_3593_);
                                if lean_obj_tag(v_quotContext_x3f_3588_) == 0 {
                                    v___x_3668_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_3568_);
                                    v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
                                    lean_inc(v_a_3669_);
                                    lean_dec_ref(v___x_3668_);
                                    v_a_3596_ = v_a_3669_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_3670_ = lean_ctor_get(v_quotContext_x3f_3588_, 0);
                                    lean_inc(v_val_3670_);
                                    v_a_3596_ = v_val_3670_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3584_);
                                lean_dec(v_openDecls_3582_);
                                lean_dec(v_currNamespace_3579_);
                                lean_dec_ref(v_opts_3576_);
                                lean_dec_ref(v_env_3571_);
                                lean_dec_ref(v_x_3566_);
                                v_a_3671_ = lean_ctor_get(v___x_3585_, 0);
                                v_isSharedCheck_3678_ = (!lean_is_exclusive(v___x_3585_)) as u8;
                                if v_isSharedCheck_3678_ == 0 {
                                    v___x_3673_ = v___x_3585_;
                                    v_isShared_3674_ = v_isSharedCheck_3678_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_3671_);
                                    lean_dec(v___x_3585_);
                                    v___x_3673_ = lean_box(0);
                                    v_isShared_3674_ = v_isSharedCheck_3678_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_openDecls_3582_);
                            lean_dec(v_currNamespace_3579_);
                            lean_dec_ref(v_opts_3576_);
                            lean_dec_ref(v_env_3571_);
                            lean_dec_ref(v_x_3566_);
                            v_a_3679_ = lean_ctor_get(v___x_3583_, 0);
                            v_isSharedCheck_3686_ = (!lean_is_exclusive(v___x_3583_)) as u8;
                            if v_isSharedCheck_3686_ == 0 {
                                v___x_3681_ = v___x_3583_;
                                v_isShared_3682_ = v_isSharedCheck_3686_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_3679_);
                                lean_dec(v___x_3583_);
                                v___x_3681_ = lean_box(0);
                                v_isShared_3682_ = v_isSharedCheck_3686_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_currNamespace_3579_);
                        lean_dec_ref(v_opts_3576_);
                        lean_dec_ref(v_env_3571_);
                        lean_dec_ref(v_x_3566_);
                        v_a_3687_ = lean_ctor_get(v___x_3580_, 0);
                        v_isSharedCheck_3694_ = (!lean_is_exclusive(v___x_3580_)) as u8;
                        if v_isSharedCheck_3694_ == 0 {
                            v___x_3689_ = v___x_3580_;
                            v_isShared_3690_ = v_isSharedCheck_3694_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3687_);
                            lean_dec(v___x_3580_);
                            v___x_3689_ = lean_box(0);
                            v_isShared_3690_ = v_isSharedCheck_3694_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_opts_3576_);
                    lean_dec_ref(v_env_3571_);
                    lean_dec_ref(v_x_3566_);
                    v_a_3695_ = lean_ctor_get(v___x_3577_, 0);
                    v_isSharedCheck_3702_ = (!lean_is_exclusive(v___x_3577_)) as u8;
                    if v_isSharedCheck_3702_ == 0 {
                        v___x_3697_ = v___x_3577_;
                        v_isShared_3698_ = v_isSharedCheck_3702_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3695_);
                        lean_dec(v___x_3577_);
                        v___x_3697_ = lean_box(0);
                        v_isShared_3698_ = v_isSharedCheck_3702_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3597_ = lean_st_ref_get(v___y_3568_);
                v_maxRecDepth_3598_ = lean_ctor_get(v___x_3597_, 5);
                lean_inc(v_maxRecDepth_3598_);
                lean_dec(v___x_3597_);
                v___x_3599_ = lean_st_ref_get(v___y_3568_);
                v_nextMacroScope_3600_ = lean_ctor_get(v___x_3599_, 4);
                lean_inc(v_nextMacroScope_3600_);
                lean_dec(v___x_3599_);
                lean_inc(v_currRecDepth_3587_);
                v___x_3601_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_3601_, 0, v_methods_3594_);
                lean_ctor_set(v___x_3601_, 1, v_a_3596_);
                lean_ctor_set(v___x_3601_, 2, v_a_3586_);
                lean_ctor_set(v___x_3601_, 3, v_currRecDepth_3587_);
                lean_ctor_set(v___x_3601_, 4, v_maxRecDepth_3598_);
                lean_ctor_set(v___x_3601_, 5, v_a_3584_);
                v___x_3602_ = lean_box(0);
                v___x_3603_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3603_, 0, v_nextMacroScope_3600_);
                lean_ctor_set(v___x_3603_, 1, v___x_3602_);
                lean_ctor_set(v___x_3603_, 2, v___x_3602_);
                v___x_3604_ = lean_apply_2(v_x_3566_, v___x_3601_, v___x_3603_);
                if lean_obj_tag(v___x_3604_) == 0 {
                    v_a_3605_ = lean_ctor_get(v___x_3604_, 1);
                    lean_inc(v_a_3605_);
                    v_a_3606_ = lean_ctor_get(v___x_3604_, 0);
                    lean_inc(v_a_3606_);
                    lean_dec_ref_known(v___x_3604_, 2);
                    v_macroScope_3607_ = lean_ctor_get(v_a_3605_, 0);
                    lean_inc(v_macroScope_3607_);
                    v_traceMsgs_3608_ = lean_ctor_get(v_a_3605_, 1);
                    lean_inc(v_traceMsgs_3608_);
                    v_expandedMacroDecls_3609_ = lean_ctor_get(v_a_3605_, 2);
                    lean_inc(v_expandedMacroDecls_3609_);
                    lean_dec(v_a_3605_);
                    v___x_3610_ = lean_box(0);
                    v___x_3611_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_expandedMacroDecls_3609_, v___x_3610_, v___y_3567_, v___y_3568_);
                    lean_dec(v_expandedMacroDecls_3609_);
                    if lean_obj_tag(v___x_3611_) == 0 {
                        lean_dec_ref_known(v___x_3611_, 1);
                        v___x_3612_ = lean_st_ref_take(v___y_3568_);
                        v_env_3613_ = lean_ctor_get(v___x_3612_, 0);
                        v_messages_3614_ = lean_ctor_get(v___x_3612_, 1);
                        v_scopes_3615_ = lean_ctor_get(v___x_3612_, 2);
                        v_usedQuotCtxts_3616_ = lean_ctor_get(v___x_3612_, 3);
                        v_maxRecDepth_3617_ = lean_ctor_get(v___x_3612_, 5);
                        v_ngen_3618_ = lean_ctor_get(v___x_3612_, 6);
                        v_auxDeclNGen_3619_ = lean_ctor_get(v___x_3612_, 7);
                        v_infoState_3620_ = lean_ctor_get(v___x_3612_, 8);
                        v_traceState_3621_ = lean_ctor_get(v___x_3612_, 9);
                        v_snapshotTasks_3622_ = lean_ctor_get(v___x_3612_, 10);
                        v_isSharedCheck_3648_ = (!lean_is_exclusive(v___x_3612_)) as u8;
                        if v_isSharedCheck_3648_ == 0 {
                            v_unused_3649_ = lean_ctor_get(v___x_3612_, 4);
                            lean_dec(v_unused_3649_);
                            v___x_3624_ = v___x_3612_;
                            v_isShared_3625_ = v_isSharedCheck_3648_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_3622_);
                            lean_inc(v_traceState_3621_);
                            lean_inc(v_infoState_3620_);
                            lean_inc(v_auxDeclNGen_3619_);
                            lean_inc(v_ngen_3618_);
                            lean_inc(v_maxRecDepth_3617_);
                            lean_inc(v_usedQuotCtxts_3616_);
                            lean_inc(v_scopes_3615_);
                            lean_inc(v_messages_3614_);
                            lean_inc(v_env_3613_);
                            lean_dec(v___x_3612_);
                            v___x_3624_ = lean_box(0);
                            v_isShared_3625_ = v_isSharedCheck_3648_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_traceMsgs_3608_);
                        lean_dec(v_macroScope_3607_);
                        lean_dec(v_a_3606_);
                        v_a_3650_ = lean_ctor_get(v___x_3611_, 0);
                        v_isSharedCheck_3657_ = (!lean_is_exclusive(v___x_3611_)) as u8;
                        if v_isSharedCheck_3657_ == 0 {
                            v___x_3652_ = v___x_3611_;
                            v_isShared_3653_ = v_isSharedCheck_3657_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3650_);
                            lean_dec(v___x_3611_);
                            v___x_3652_ = lean_box(0);
                            v_isShared_3653_ = v_isSharedCheck_3657_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_3658_ = lean_ctor_get(v___x_3604_, 0);
                    lean_inc(v_a_3658_);
                    lean_dec_ref_known(v___x_3604_, 2);
                    if lean_obj_tag(v_a_3658_) == 0 {
                        v_a_3659_ = lean_ctor_get(v_a_3658_, 0);
                        lean_inc(v_a_3659_);
                        v_a_3660_ = lean_ctor_get(v_a_3658_, 1);
                        lean_inc_ref(v_a_3660_);
                        lean_dec_ref_known(v_a_3658_, 2);
                        v___x_3661_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0;
                        v___x_3662_ = lean_string_dec_eq(v_a_3660_, v___x_3661_);
                        if v___x_3662_ == 0 {
                            v___x_3663_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_3663_, 0, v_a_3660_);
                            v___x_3664_ = l_Lean_MessageData_ofFormat(v___x_3663_);
                            v___x_3665_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_a_3659_, v___x_3664_, v___y_3567_, v___y_3568_);
                            lean_dec(v_a_3659_);
                            return v___x_3665_;
                        } else {
                            lean_dec_ref(v_a_3660_);
                            v___x_3666_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_a_3659_);
                            return v___x_3666_;
                        }
                    } else {
                        v___x_3667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
                        return v___x_3667_;
                    }
                }
            }
            2 => {
                if v_isShared_3625_ == 0 {
                    lean_ctor_set(v___x_3624_, 4, v_macroScope_3607_);
                    v___x_3627_ = v___x_3624_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_env_3613_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_messages_3614_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 2, v_scopes_3615_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 3, v_usedQuotCtxts_3616_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 4, v_macroScope_3607_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 5, v_maxRecDepth_3617_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 6, v_ngen_3618_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 7, v_auxDeclNGen_3619_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 8, v_infoState_3620_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 9, v_traceState_3621_);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 10, v_snapshotTasks_3622_);
                    v___x_3627_ = v_reuseFailAlloc_3647_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3628_ = lean_st_ref_set(v___y_3568_, v___x_3627_);
                v___x_3629_ = l_List_reverse___redArg(v_traceMsgs_3608_);
                v___x_3630_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v___x_3629_, v___y_3567_, v___y_3568_);
                if lean_obj_tag(v___x_3630_) == 0 {
                    v_isSharedCheck_3637_ = (!lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3637_ == 0 {
                        v_unused_3638_ = lean_ctor_get(v___x_3630_, 0);
                        lean_dec(v_unused_3638_);
                        v___x_3632_ = v___x_3630_;
                        v_isShared_3633_ = v_isSharedCheck_3637_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_3630_);
                        v___x_3632_ = lean_box(0);
                        v_isShared_3633_ = v_isSharedCheck_3637_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3606_);
                    v_a_3639_ = lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3646_ = (!lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3641_ = v___x_3630_;
                        v_isShared_3642_ = v_isSharedCheck_3646_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3639_);
                        lean_dec(v___x_3630_);
                        v___x_3641_ = lean_box(0);
                        v_isShared_3642_ = v_isSharedCheck_3646_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3633_ == 0 {
                    lean_ctor_set(v___x_3632_, 0, v_a_3606_);
                    v___x_3635_ = v___x_3632_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3606_);
                    v___x_3635_ = v_reuseFailAlloc_3636_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3635_;
            }
            6 => {
                if v_isShared_3642_ == 0 {
                    v___x_3644_ = v___x_3641_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3644_;
            }
            8 => {
                if v_isShared_3653_ == 0 {
                    v___x_3655_ = v___x_3652_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
                    v___x_3655_ = v_reuseFailAlloc_3656_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3655_;
            }
            10 => {
                if v_isShared_3674_ == 0 {
                    v___x_3676_ = v___x_3673_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
                    v___x_3676_ = v_reuseFailAlloc_3677_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3676_;
            }
            12 => {
                if v_isShared_3682_ == 0 {
                    v___x_3684_ = v___x_3681_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
                    v___x_3684_ = v_reuseFailAlloc_3685_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3684_;
            }
            14 => {
                if v_isShared_3690_ == 0 {
                    v___x_3692_ = v___x_3689_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
                    v___x_3692_ = v_reuseFailAlloc_3693_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3692_;
            }
            16 => {
                if v_isShared_3698_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(
    mut v_x_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3707_: *mut LeanObject = core::ptr::null_mut();
    v_res_3707_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(
            v_x_3703_,
            v___y_3704_,
            v___y_3705_,
        );
    lean_dec(v___y_3705_);
    lean_dec_ref(v___y_3704_);
    return v_res_3707_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7() -> *mut LeanObject {
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    v___x_3722_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
    v___x_3723_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11;
    v___x_3724_ = l_Lean_Name_append(v___x_3723_, v___x_3722_);
    return v___x_3724_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9() -> *mut LeanObject {
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    v___x_3726_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__8;
    v___x_3727_ = l_Lean_stringToMessageData(v___x_3726_);
    return v___x_3727_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11() -> *mut LeanObject {
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__10;
    v___x_3730_ = l_Lean_stringToMessageData(v___x_3729_);
    return v___x_3730_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfInstance(
    mut v_modifiers_3731_: *mut LeanObject,
    mut v_stx_3732_: *mut LeanObject,
    mut v_a_3733_: *mut LeanObject,
    mut v_a_3734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declId_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3831_: u8 = 0;
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_a_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut v_a_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3862_: u8 = 0;
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut v_val_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3875_: u8 = 0;
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3887_: u8 = 0;
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v_a_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v_a_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_reuseFailAlloc_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_a_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_a_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3947_: u8 = 0;
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3951_: u8 = 0;
    let mut v_a_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3736_ = lean_unsigned_to_nat(0);
                v___x_3756_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3736_);
                v___x_3757_ = lean_alloc_closure(
                    l_Lean_Elab_toAttributeKind___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___x_3757_, 0, v___x_3756_);
                v___x_3758_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_3757_, v_a_3733_, v_a_3734_);
                if lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
                    lean_inc(v_a_3759_);
                    lean_dec_ref_known(v___x_3758_, 1);
                    v___x_3760_ = lean_unsigned_to_nat(2);
                    v___x_3783_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3760_);
                    v___x_3784_ = lean_alloc_closure(
                        l_Lean_Elab_expandOptNamedPrio___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___x_3784_, 0, v___x_3783_);
                    v___x_3785_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_3784_, v_a_3733_, v_a_3734_);
                    if lean_obj_tag(v___x_3785_) == 0 {
                        v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
                        lean_inc(v_a_3786_);
                        lean_dec_ref_known(v___x_3785_, 1);
                        v___x_3787_ = l_Lean_Elab_Command_getRef___redArg(v_a_3733_);
                        if lean_obj_tag(v___x_3787_) == 0 {
                            v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
                            lean_inc(v_a_3788_);
                            lean_dec_ref_known(v___x_3787_, 1);
                            v___x_3789_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_3733_);
                            if lean_obj_tag(v___x_3789_) == 0 {
                                lean_dec_ref_known(v___x_3789_, 1);
                                v_quotContext_x3f_3790_ = lean_ctor_get(v_a_3733_, 5);
                                v___x_3791_ = 0;
                                v___x_3792_ = l_Lean_SourceInfo_fromRef(v_a_3788_, v___x_3791_);
                                lean_dec(v_a_3788_);
                                if lean_obj_tag(v_quotContext_x3f_3790_) == 0 {
                                    v___x_3927_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_3734_);
                                    lean_dec_ref(v___x_3927_);
                                    state = 3;
                                    continue;
                                } else {
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3788_);
                                lean_dec(v_a_3786_);
                                lean_dec(v_a_3759_);
                                lean_dec(v_stx_3732_);
                                lean_dec_ref(v_modifiers_3731_);
                                v_a_3928_ = lean_ctor_get(v___x_3789_, 0);
                                v_isSharedCheck_3935_ = (!lean_is_exclusive(v___x_3789_)) as u8;
                                if v_isSharedCheck_3935_ == 0 {
                                    v___x_3930_ = v___x_3789_;
                                    v_isShared_3931_ = v_isSharedCheck_3935_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_3928_);
                                    lean_dec(v___x_3789_);
                                    v___x_3930_ = lean_box(0);
                                    v_isShared_3931_ = v_isSharedCheck_3935_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3786_);
                            lean_dec(v_a_3759_);
                            lean_dec(v_stx_3732_);
                            lean_dec_ref(v_modifiers_3731_);
                            v_a_3936_ = lean_ctor_get(v___x_3787_, 0);
                            v_isSharedCheck_3943_ = (!lean_is_exclusive(v___x_3787_)) as u8;
                            if v_isSharedCheck_3943_ == 0 {
                                v___x_3938_ = v___x_3787_;
                                v_isShared_3939_ = v_isSharedCheck_3943_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_3936_);
                                lean_dec(v___x_3787_);
                                v___x_3938_ = lean_box(0);
                                v_isShared_3939_ = v_isSharedCheck_3943_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3759_);
                        lean_dec(v_stx_3732_);
                        lean_dec_ref(v_modifiers_3731_);
                        v_a_3944_ = lean_ctor_get(v___x_3785_, 0);
                        v_isSharedCheck_3951_ = (!lean_is_exclusive(v___x_3785_)) as u8;
                        if v_isSharedCheck_3951_ == 0 {
                            v___x_3946_ = v___x_3785_;
                            v_isShared_3947_ = v_isSharedCheck_3951_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_3944_);
                            lean_dec(v___x_3785_);
                            v___x_3946_ = lean_box(0);
                            v_isShared_3947_ = v_isSharedCheck_3951_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_stx_3732_);
                    lean_dec_ref(v_modifiers_3731_);
                    v_a_3952_ = lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3959_ = (!lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3959_ == 0 {
                        v___x_3954_ = v___x_3758_;
                        v_isShared_3955_ = v_isSharedCheck_3959_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_3952_);
                        lean_dec(v___x_3758_);
                        v___x_3954_ = lean_box(0);
                        v_isShared_3955_ = v_isSharedCheck_3959_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v_docString_x3f_3744_ = lean_ctor_get(v___y_3740_, 1);
                lean_inc(v_docString_x3f_3744_);
                v___x_3745_ = 1;
                v___x_3746_ = l_Lean_Syntax_getArgs(v_stx_3732_);
                v___x_3747_ = lean_unsigned_to_nat(5);
                v___x_3748_ = l_Array_toSubarray___redArg(v___x_3746_, v___x_3736_, v___x_3747_);
                v___x_3749_ = l_Subarray_copy___redArg(v___x_3748_);
                v___x_3750_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3750_, 0, v___y_3738_);
                lean_ctor_set(v___x_3750_, 1, v___y_3741_);
                lean_ctor_set(v___x_3750_, 2, v___x_3749_);
                v___x_3751_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3751_, 0, v___y_3739_);
                v___x_3752_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3747_);
                v___x_3753_ = lean_box(0);
                v___x_3754_ = lean_alloc_ctor(0, 10, (1) as u32);
                lean_ctor_set(v___x_3754_, 0, v_stx_3732_);
                lean_ctor_set(v___x_3754_, 1, v___x_3750_);
                lean_ctor_set(v___x_3754_, 2, v___y_3740_);
                lean_ctor_set(v___x_3754_, 3, v_declId_3743_);
                lean_ctor_set(v___x_3754_, 4, v___y_3742_);
                lean_ctor_set(v___x_3754_, 5, v___x_3751_);
                lean_ctor_set(v___x_3754_, 6, v___x_3752_);
                lean_ctor_set(v___x_3754_, 7, v_docString_x3f_3744_);
                lean_ctor_set(v___x_3754_, 8, v___x_3753_);
                lean_ctor_set(v___x_3754_, 9, v___x_3753_);
                lean_ctor_set_uint8(
                    v___x_3754_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    v___x_3745_,
                );
                v___x_3755_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3755_, 0, v___x_3754_);
                return v___x_3755_;
            }
            2 => {
                v___x_3770_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__0;
                v___x_3771_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__1;
                lean_inc_ref(v___y_3764_);
                lean_inc_ref(v___y_3768_);
                v___x_3772_ =
                    l_Lean_Name_mkStr4(v___y_3768_, v___y_3764_, v___x_3770_, v___x_3771_);
                v___x_3773_ = lean_unsigned_to_nat(1);
                v___x_3774_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3773_);
                v___x_3775_ = 1;
                v___x_3776_ = l_Lean_mkIdentFrom(v___x_3774_, v___y_3765_, v___x_3775_);
                lean_dec(v___x_3774_);
                v___x_3777_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0;
                lean_inc(v___y_3767_);
                lean_inc_n(v___y_3762_, 2);
                v___x_3778_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3778_, 0, v___y_3762_);
                lean_ctor_set(v___x_3778_, 1, v___y_3767_);
                lean_ctor_set(v___x_3778_, 2, v___x_3777_);
                v___x_3779_ = lean_mk_empty_array_with_capacity(v___x_3760_);
                v___x_3780_ = lean_array_push(v___x_3779_, v___x_3776_);
                v___x_3781_ = lean_array_push(v___x_3780_, v___x_3778_);
                v___x_3782_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3782_, 0, v___y_3762_);
                lean_ctor_set(v___x_3782_, 1, v___x_3772_);
                lean_ctor_set(v___x_3782_, 2, v___x_3781_);
                v___y_3738_ = v___y_3762_;
                v___y_3739_ = v___y_3763_;
                v___y_3740_ = v___y_3766_;
                v___y_3741_ = v___y_3767_;
                v___y_3742_ = v___y_3769_;
                v_declId_3743_ = v___x_3782_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3794_ = lean_unsigned_to_nat(4);
                v___x_3795_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3794_);
                v___x_3796_ = l_Lean_Elab_expandDeclSig(v___x_3795_);
                lean_dec(v___x_3795_);
                v_fst_3797_ = lean_ctor_get(v___x_3796_, 0);
                v_snd_3798_ = lean_ctor_get(v___x_3796_, 1);
                v_isSharedCheck_3926_ = (!lean_is_exclusive(v___x_3796_)) as u8;
                if v_isSharedCheck_3926_ == 0 {
                    v___x_3800_ = v___x_3796_;
                    v_isShared_3801_ = v_isSharedCheck_3926_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_3798_);
                    lean_inc(v_fst_3797_);
                    lean_dec(v___x_3796_);
                    v___x_3800_ = lean_box(0);
                    v_isShared_3801_ = v_isSharedCheck_3926_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3802_ = l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_;
                v___x_3803_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__2;
                v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0;
                v___x_3805_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__4;
                lean_inc(v___x_3792_);
                if v_isShared_3801_ == 0 {
                    lean_ctor_set_tag(v___x_3800_, 2);
                    lean_ctor_set(v___x_3800_, 1, v___x_3804_);
                    lean_ctor_set(v___x_3800_, 0, v___x_3792_);
                    v___x_3807_ = v___x_3800_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3792_);
                    lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3804_);
                    v___x_3807_ = v_reuseFailAlloc_3925_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3808_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_3809_ = l_Nat_reprFast(v_a_3786_);
                v___x_3810_ = lean_box(2);
                v___x_3811_ = l_Lean_Syntax_mkNumLit(v___x_3809_, v___x_3810_);
                lean_inc(v___x_3792_);
                v___x_3812_ = l_Lean_Syntax_node1(v___x_3792_, v___x_3808_, v___x_3811_);
                v___x_3813_ =
                    l_Lean_Syntax_node2(v___x_3792_, v___x_3805_, v___x_3807_, v___x_3812_);
                v___x_3814_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1;
                v___x_3815_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3815_, 0, v___x_3814_);
                lean_ctor_set(v___x_3815_, 1, v___x_3813_);
                v___x_3816_ = (lean_unbox(v_a_3759_) as u8);
                lean_dec(v_a_3759_);
                lean_ctor_set_uint8(
                    v___x_3815_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3816_,
                );
                v___x_3817_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_3731_, v___x_3815_);
                v___x_3818_ = lean_unsigned_to_nat(3);
                v___x_3819_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3818_);
                v___x_3820_ = l_Lean_Syntax_getOptional_x3f(v___x_3819_);
                lean_dec(v___x_3819_);
                if lean_obj_tag(v___x_3820_) == 0 {
                    v___x_3821_ = l_Lean_Syntax_getArgs(v_fst_3797_);
                    lean_inc(v_snd_3798_);
                    v___x_3822_ = l_Lean_Elab_Command_mkInstanceName(
                        v___x_3821_,
                        v_snd_3798_,
                        v_a_3733_,
                        v_a_3734_,
                    );
                    if lean_obj_tag(v___x_3822_) == 0 {
                        v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
                        lean_inc(v_a_3823_);
                        lean_dec_ref_known(v___x_3822_, 1);
                        v___x_3824_ = l_Lean_inheritedTraceOptions;
                        v___x_3825_ = lean_st_ref_get(v___x_3824_);
                        v___x_3826_ = lean_st_ref_get(v_a_3734_);
                        v_scopes_3827_ = lean_ctor_get(v___x_3826_, 2);
                        lean_inc(v_scopes_3827_);
                        lean_dec(v___x_3826_);
                        v___x_3828_ = l_Lean_Elab_Command_instInhabitedScope_default;
                        v___x_3829_ = l_List_head_x21___redArg(v___x_3828_, v_scopes_3827_);
                        lean_dec(v_scopes_3827_);
                        v_opts_3830_ = lean_ctor_get(v___x_3829_, 1);
                        lean_inc_ref(v_opts_3830_);
                        lean_dec(v___x_3829_);
                        v_hasTrace_3831_ = lean_ctor_get_uint8(
                            v_opts_3830_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3831_ == 0 {
                            lean_dec_ref(v_opts_3830_);
                            lean_dec(v___x_3825_);
                            v___y_3762_ = v___x_3810_;
                            v___y_3763_ = v_snd_3798_;
                            v___y_3764_ = v___x_3803_;
                            v___y_3765_ = v_a_3823_;
                            v___y_3766_ = v___x_3817_;
                            v___y_3767_ = v___x_3808_;
                            v___y_3768_ = v___x_3802_;
                            v___y_3769_ = v_fst_3797_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3832_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
                            v___x_3833_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_mkDefViewOfInstance___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once
                                ),
                                _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7,
                            );
                            v___x_3834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v___x_3825_,
                                v_opts_3830_,
                                v___x_3833_,
                            );
                            lean_dec_ref(v_opts_3830_);
                            lean_dec(v___x_3825_);
                            if v___x_3834_ == 0 {
                                v___y_3762_ = v___x_3810_;
                                v___y_3763_ = v_snd_3798_;
                                v___y_3764_ = v___x_3803_;
                                v___y_3765_ = v_a_3823_;
                                v___y_3766_ = v___x_3817_;
                                v___y_3767_ = v___x_3808_;
                                v___y_3768_ = v___x_3802_;
                                v___y_3769_ = v_fst_3797_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3835_ = l_Lean_Elab_Command_getScope___redArg(v_a_3734_);
                                if lean_obj_tag(v___x_3835_) == 0 {
                                    v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
                                    lean_inc(v_a_3836_);
                                    lean_dec_ref_known(v___x_3835_, 1);
                                    v_currNamespace_3837_ = lean_ctor_get(v_a_3836_, 2);
                                    lean_inc(v_currNamespace_3837_);
                                    lean_dec(v_a_3836_);
                                    v___x_3838_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once), _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
                                    lean_inc(v_a_3823_);
                                    v___x_3839_ =
                                        l_Lean_Name_append(v_currNamespace_3837_, v_a_3823_);
                                    v___x_3840_ = l_Lean_MessageData_ofName(v___x_3839_);
                                    v___x_3841_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3841_, 0, v___x_3838_);
                                    lean_ctor_set(v___x_3841_, 1, v___x_3840_);
                                    v___x_3842_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_3832_, v___x_3841_, v_a_3733_, v_a_3734_);
                                    if lean_obj_tag(v___x_3842_) == 0 {
                                        lean_dec_ref_known(v___x_3842_, 1);
                                        v___y_3762_ = v___x_3810_;
                                        v___y_3763_ = v_snd_3798_;
                                        v___y_3764_ = v___x_3803_;
                                        v___y_3765_ = v_a_3823_;
                                        v___y_3766_ = v___x_3817_;
                                        v___y_3767_ = v___x_3808_;
                                        v___y_3768_ = v___x_3802_;
                                        v___y_3769_ = v_fst_3797_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_a_3823_);
                                        lean_dec_ref(v___x_3817_);
                                        lean_dec(v_snd_3798_);
                                        lean_dec(v_fst_3797_);
                                        lean_dec(v_stx_3732_);
                                        v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
                                        v_isSharedCheck_3850_ =
                                            (!lean_is_exclusive(v___x_3842_)) as u8;
                                        if v_isSharedCheck_3850_ == 0 {
                                            v___x_3845_ = v___x_3842_;
                                            v_isShared_3846_ = v_isSharedCheck_3850_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3843_);
                                            lean_dec(v___x_3842_);
                                            v___x_3845_ = lean_box(0);
                                            v_isShared_3846_ = v_isSharedCheck_3850_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_3823_);
                                    lean_dec_ref(v___x_3817_);
                                    lean_dec(v_snd_3798_);
                                    lean_dec(v_fst_3797_);
                                    lean_dec(v_stx_3732_);
                                    v_a_3851_ = lean_ctor_get(v___x_3835_, 0);
                                    v_isSharedCheck_3858_ = (!lean_is_exclusive(v___x_3835_)) as u8;
                                    if v_isSharedCheck_3858_ == 0 {
                                        v___x_3853_ = v___x_3835_;
                                        v_isShared_3854_ = v_isSharedCheck_3858_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3851_);
                                        lean_dec(v___x_3835_);
                                        v___x_3853_ = lean_box(0);
                                        v_isShared_3854_ = v_isSharedCheck_3858_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3817_);
                        lean_dec(v_snd_3798_);
                        lean_dec(v_fst_3797_);
                        lean_dec(v_stx_3732_);
                        v_a_3859_ = lean_ctor_get(v___x_3822_, 0);
                        v_isSharedCheck_3866_ = (!lean_is_exclusive(v___x_3822_)) as u8;
                        if v_isSharedCheck_3866_ == 0 {
                            v___x_3861_ = v___x_3822_;
                            v_isShared_3862_ = v_isSharedCheck_3866_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3859_);
                            lean_dec(v___x_3822_);
                            v___x_3861_ = lean_box(0);
                            v_isShared_3862_ = v_isSharedCheck_3866_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v_val_3867_ = lean_ctor_get(v___x_3820_, 0);
                    lean_inc(v_val_3867_);
                    lean_dec_ref_known(v___x_3820_, 1);
                    v___x_3868_ = l_Lean_inheritedTraceOptions;
                    v___x_3869_ = lean_st_ref_get(v___x_3868_);
                    v___x_3870_ = lean_st_ref_get(v_a_3734_);
                    v_scopes_3871_ = lean_ctor_get(v___x_3870_, 2);
                    lean_inc(v_scopes_3871_);
                    lean_dec(v___x_3870_);
                    v___x_3872_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3873_ = l_List_head_x21___redArg(v___x_3872_, v_scopes_3871_);
                    lean_dec(v_scopes_3871_);
                    v_opts_3874_ = lean_ctor_get(v___x_3873_, 1);
                    lean_inc_ref(v_opts_3874_);
                    lean_dec(v___x_3873_);
                    v_hasTrace_3875_ = lean_ctor_get_uint8(
                        v_opts_3874_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3875_ == 0 {
                        lean_dec_ref(v_opts_3874_);
                        lean_dec(v___x_3869_);
                        v___y_3738_ = v___x_3810_;
                        v___y_3739_ = v_snd_3798_;
                        v___y_3740_ = v___x_3817_;
                        v___y_3741_ = v___x_3808_;
                        v___y_3742_ = v_fst_3797_;
                        v_declId_3743_ = v_val_3867_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3876_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
                        v___x_3877_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_mkDefViewOfInstance___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once
                            ),
                            _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7,
                        );
                        v___x_3878_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_3869_,
                            v_opts_3874_,
                            v___x_3877_,
                        );
                        lean_dec_ref(v_opts_3874_);
                        lean_dec(v___x_3869_);
                        if v___x_3878_ == 0 {
                            v___y_3738_ = v___x_3810_;
                            v___y_3739_ = v_snd_3798_;
                            v___y_3740_ = v___x_3817_;
                            v___y_3741_ = v___x_3808_;
                            v___y_3742_ = v_fst_3797_;
                            v_declId_3743_ = v_val_3867_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3879_ = l_Lean_Syntax_getArgs(v_fst_3797_);
                            lean_inc(v_snd_3798_);
                            v___x_3880_ = l_Lean_Elab_Command_mkInstanceName(
                                v___x_3879_,
                                v_snd_3798_,
                                v_a_3733_,
                                v_a_3734_,
                            );
                            if lean_obj_tag(v___x_3880_) == 0 {
                                v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
                                lean_inc(v_a_3881_);
                                lean_dec_ref_known(v___x_3880_, 1);
                                v___x_3882_ = lean_st_ref_get(v___x_3868_);
                                v___x_3883_ = lean_st_ref_get(v_a_3734_);
                                v_scopes_3884_ = lean_ctor_get(v___x_3883_, 2);
                                lean_inc(v_scopes_3884_);
                                lean_dec(v___x_3883_);
                                v___x_3885_ = l_List_head_x21___redArg(v___x_3872_, v_scopes_3884_);
                                lean_dec(v_scopes_3884_);
                                v_opts_3886_ = lean_ctor_get(v___x_3885_, 1);
                                lean_inc_ref(v_opts_3886_);
                                lean_dec(v___x_3885_);
                                v_hasTrace_3887_ = lean_ctor_get_uint8(
                                    v_opts_3886_,
                                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                );
                                if v_hasTrace_3887_ == 0 {
                                    lean_dec_ref(v_opts_3886_);
                                    lean_dec(v___x_3882_);
                                    lean_dec(v_a_3881_);
                                    v___y_3738_ = v___x_3810_;
                                    v___y_3739_ = v_snd_3798_;
                                    v___y_3740_ = v___x_3817_;
                                    v___y_3741_ = v___x_3808_;
                                    v___y_3742_ = v_fst_3797_;
                                    v_declId_3743_ = v_val_3867_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3888_ =
                                        l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                            v___x_3882_,
                                            v_opts_3886_,
                                            v___x_3877_,
                                        );
                                    lean_dec_ref(v_opts_3886_);
                                    lean_dec(v___x_3882_);
                                    if v___x_3888_ == 0 {
                                        lean_dec(v_a_3881_);
                                        v___y_3738_ = v___x_3810_;
                                        v___y_3739_ = v_snd_3798_;
                                        v___y_3740_ = v___x_3817_;
                                        v___y_3741_ = v___x_3808_;
                                        v___y_3742_ = v_fst_3797_;
                                        v_declId_3743_ = v_val_3867_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3889_ =
                                            l_Lean_Elab_Command_getScope___redArg(v_a_3734_);
                                        if lean_obj_tag(v___x_3889_) == 0 {
                                            v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
                                            lean_inc(v_a_3890_);
                                            lean_dec_ref_known(v___x_3889_, 1);
                                            v_currNamespace_3891_ = lean_ctor_get(v_a_3890_, 2);
                                            lean_inc(v_currNamespace_3891_);
                                            lean_dec(v_a_3890_);
                                            v___x_3892_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once), _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
                                            v___x_3893_ = l_Lean_Name_append(
                                                v_currNamespace_3891_,
                                                v_a_3881_,
                                            );
                                            v___x_3894_ = l_Lean_MessageData_ofName(v___x_3893_);
                                            v___x_3895_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_3895_, 0, v___x_3892_);
                                            lean_ctor_set(v___x_3895_, 1, v___x_3894_);
                                            v___x_3896_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once), _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11);
                                            v___x_3897_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_3897_, 0, v___x_3895_);
                                            lean_ctor_set(v___x_3897_, 1, v___x_3896_);
                                            lean_inc(v_val_3867_);
                                            v___x_3898_ = l_Lean_MessageData_ofSyntax(v_val_3867_);
                                            v___x_3899_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_3899_, 0, v___x_3897_);
                                            lean_ctor_set(v___x_3899_, 1, v___x_3898_);
                                            v___x_3900_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_3876_, v___x_3899_, v_a_3733_, v_a_3734_);
                                            if lean_obj_tag(v___x_3900_) == 0 {
                                                lean_dec_ref_known(v___x_3900_, 1);
                                                v___y_3738_ = v___x_3810_;
                                                v___y_3739_ = v_snd_3798_;
                                                v___y_3740_ = v___x_3817_;
                                                v___y_3741_ = v___x_3808_;
                                                v___y_3742_ = v_fst_3797_;
                                                v_declId_3743_ = v_val_3867_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec(v_val_3867_);
                                                lean_dec_ref(v___x_3817_);
                                                lean_dec(v_snd_3798_);
                                                lean_dec(v_fst_3797_);
                                                lean_dec(v_stx_3732_);
                                                v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
                                                v_isSharedCheck_3908_ =
                                                    (!lean_is_exclusive(v___x_3900_)) as u8;
                                                if v_isSharedCheck_3908_ == 0 {
                                                    v___x_3903_ = v___x_3900_;
                                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3901_);
                                                    lean_dec(v___x_3900_);
                                                    v___x_3903_ = lean_box(0);
                                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                                    state = 12;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_3881_);
                                            lean_dec(v_val_3867_);
                                            lean_dec_ref(v___x_3817_);
                                            lean_dec(v_snd_3798_);
                                            lean_dec(v_fst_3797_);
                                            lean_dec(v_stx_3732_);
                                            v_a_3909_ = lean_ctor_get(v___x_3889_, 0);
                                            v_isSharedCheck_3916_ =
                                                (!lean_is_exclusive(v___x_3889_)) as u8;
                                            if v_isSharedCheck_3916_ == 0 {
                                                v___x_3911_ = v___x_3889_;
                                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                                state = 14;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3909_);
                                                lean_dec(v___x_3889_);
                                                v___x_3911_ = lean_box(0);
                                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_val_3867_);
                                lean_dec_ref(v___x_3817_);
                                lean_dec(v_snd_3798_);
                                lean_dec(v_fst_3797_);
                                lean_dec(v_stx_3732_);
                                v_a_3917_ = lean_ctor_get(v___x_3880_, 0);
                                v_isSharedCheck_3924_ = (!lean_is_exclusive(v___x_3880_)) as u8;
                                if v_isSharedCheck_3924_ == 0 {
                                    v___x_3919_ = v___x_3880_;
                                    v_isShared_3920_ = v_isSharedCheck_3924_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_3917_);
                                    lean_dec(v___x_3880_);
                                    v___x_3919_ = lean_box(0);
                                    v_isShared_3920_ = v_isSharedCheck_3924_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_3846_ == 0 {
                    v___x_3848_ = v___x_3845_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
                    v___x_3848_ = v_reuseFailAlloc_3849_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3848_;
            }
            8 => {
                if v_isShared_3854_ == 0 {
                    v___x_3856_ = v___x_3853_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
                    v___x_3856_ = v_reuseFailAlloc_3857_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3856_;
            }
            10 => {
                if v_isShared_3862_ == 0 {
                    v___x_3864_ = v___x_3861_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
                    v___x_3864_ = v_reuseFailAlloc_3865_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3864_;
            }
            12 => {
                if v_isShared_3904_ == 0 {
                    v___x_3906_ = v___x_3903_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
                    v___x_3906_ = v_reuseFailAlloc_3907_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3906_;
            }
            14 => {
                if v_isShared_3912_ == 0 {
                    v___x_3914_ = v___x_3911_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
                    v___x_3914_ = v_reuseFailAlloc_3915_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3914_;
            }
            16 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3922_;
            }
            18 => {
                if v_isShared_3931_ == 0 {
                    v___x_3933_ = v___x_3930_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3933_;
            }
            20 => {
                if v_isShared_3939_ == 0 {
                    v___x_3941_ = v___x_3938_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3941_;
            }
            22 => {
                if v_isShared_3947_ == 0 {
                    v___x_3949_ = v___x_3946_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
                    v___x_3949_ = v_reuseFailAlloc_3950_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3949_;
            }
            24 => {
                if v_isShared_3955_ == 0 {
                    v___x_3957_ = v___x_3954_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
                    v___x_3957_ = v_reuseFailAlloc_3958_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfInstance___boxed(
    mut v_modifiers_3960_: *mut LeanObject,
    mut v_stx_3961_: *mut LeanObject,
    mut v_a_3962_: *mut LeanObject,
    mut v_a_3963_: *mut LeanObject,
    mut v_a_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3965_: *mut LeanObject = core::ptr::null_mut();
    v_res_3965_ = l_Lean_Elab_Command_mkDefViewOfInstance(
        v_modifiers_3960_,
        v_stx_3961_,
        v_a_3962_,
        v_a_3963_,
    );
    lean_dec(v_a_3963_);
    lean_dec_ref(v_a_3962_);
    return v_res_3965_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(
    mut v_00_u03b1_3966_: *mut LeanObject,
    mut v_x_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    v___x_3970_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_3967_, v___y_3969_);
    return v___x_3970_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(
    mut v_00_u03b1_3971_: *mut LeanObject,
    mut v_x_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
    mut v___y_3974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3975_: *mut LeanObject = core::ptr::null_mut();
    v_res_3975_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(v_00_u03b1_3971_, v_x_3972_, v___y_3973_, v___y_3974_);
    lean_dec_ref(v___y_3973_);
    lean_dec_ref(v_x_3972_);
    return v_res_3975_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(
    mut v_00_u03b1_3976_: *mut LeanObject,
    mut v_ref_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    v___x_3981_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_3977_);
    return v___x_3981_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(
    mut v_00_u03b1_3982_: *mut LeanObject,
    mut v_ref_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3987_: *mut LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(v_00_u03b1_3982_, v_ref_3983_, v___y_3984_, v___y_3985_);
    lean_dec(v___y_3985_);
    lean_dec_ref(v___y_3984_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(
    mut v_00_u03b1_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3992_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
    return v___x_3992_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(
    mut v_00_u03b1_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3997_: *mut LeanObject = core::ptr::null_mut();
    v_res_3997_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(v_00_u03b1_3993_, v___y_3994_, v___y_3995_);
    lean_dec(v___y_3995_);
    lean_dec_ref(v___y_3994_);
    return v_res_3997_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(
    mut v_00_u03b1_3998_: *mut LeanObject,
    mut v_x_3999_: *mut LeanObject,
    mut v___y_4000_: *mut LeanObject,
    mut v___y_4001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    v___x_4003_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(
            v_x_3999_,
            v___y_4000_,
            v___y_4001_,
        );
    return v___x_4003_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(
    mut v_00_u03b1_4004_: *mut LeanObject,
    mut v_x_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4009_: *mut LeanObject = core::ptr::null_mut();
    v_res_4009_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(
        v_00_u03b1_4004_,
        v_x_4005_,
        v___y_4006_,
        v___y_4007_,
    );
    lean_dec(v___y_4007_);
    lean_dec_ref(v___y_4006_);
    return v_res_4009_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(
    mut v_msgData_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    v___x_4014_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_4010_, v___y_4012_);
    return v___x_4014_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___boxed(
    mut v_msgData_4015_: *mut LeanObject,
    mut v___y_4016_: *mut LeanObject,
    mut v___y_4017_: *mut LeanObject,
    mut v___y_4018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4019_: *mut LeanObject = core::ptr::null_mut();
    v_res_4019_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(v_msgData_4015_, v___y_4016_, v___y_4017_);
    lean_dec(v___y_4017_);
    lean_dec_ref(v___y_4016_);
    return v_res_4019_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(
    mut v_as_4020_: *mut LeanObject,
    mut v_as_x27_4021_: *mut LeanObject,
    mut v_b_4022_: *mut LeanObject,
    mut v_a_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_4021_, v_b_4022_, v___y_4024_, v___y_4025_);
    return v___x_4027_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(
    mut v_as_4028_: *mut LeanObject,
    mut v_as_x27_4029_: *mut LeanObject,
    mut v_b_4030_: *mut LeanObject,
    mut v_a_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4035_: *mut LeanObject = core::ptr::null_mut();
    v_res_4035_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(v_as_4028_, v_as_x27_4029_, v_b_4030_, v_a_4031_, v___y_4032_, v___y_4033_);
    lean_dec(v___y_4033_);
    lean_dec_ref(v___y_4032_);
    lean_dec(v_as_x27_4029_);
    lean_dec(v_as_4028_);
    return v_res_4035_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(
    mut v_00_u03b1_4036_: *mut LeanObject,
    mut v_ref_4037_: *mut LeanObject,
    mut v_msg_4038_: *mut LeanObject,
    mut v___y_4039_: *mut LeanObject,
    mut v___y_4040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    v___x_4042_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_4037_, v_msg_4038_, v___y_4039_, v___y_4040_);
    return v___x_4042_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(
    mut v_00_u03b1_4043_: *mut LeanObject,
    mut v_ref_4044_: *mut LeanObject,
    mut v_msg_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4049_: *mut LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(v_00_u03b1_4043_, v_ref_4044_, v_msg_4045_, v___y_4046_, v___y_4047_);
    lean_dec(v___y_4047_);
    lean_dec_ref(v___y_4046_);
    lean_dec(v_ref_4044_);
    return v_res_4049_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4050_: *mut LeanObject,
    mut v_m_4051_: *mut LeanObject,
    mut v_a_4052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_4051_, v_a_4052_);
    return v___x_4053_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_4054_: *mut LeanObject,
    mut v_m_4055_: *mut LeanObject,
    mut v_a_4056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4057_: *mut LeanObject = core::ptr::null_mut();
    v_res_4057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v_00_u03b2_4054_, v_m_4055_, v_a_4056_);
    lean_dec(v_a_4056_);
    lean_dec_ref(v_m_4055_);
    return v_res_4057_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(
    mut v_00_u03b1_4058_: *mut LeanObject,
    mut v_msg_4059_: *mut LeanObject,
    mut v___y_4060_: *mut LeanObject,
    mut v___y_4061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_4059_, v___y_4060_, v___y_4061_);
    return v___x_4063_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___boxed(
    mut v_00_u03b1_4064_: *mut LeanObject,
    mut v_msg_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4069_: *mut LeanObject = core::ptr::null_mut();
    v_res_4069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(v_00_u03b1_4064_, v_msg_4065_, v___y_4066_, v___y_4067_);
    lean_dec(v___y_4067_);
    lean_dec_ref(v___y_4066_);
    return v_res_4069_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(
    mut v_00_u03b2_4070_: *mut LeanObject,
    mut v_x_4071_: *mut LeanObject,
    mut v_x_4072_: *mut LeanObject,
) -> u8 {
    let mut v___x_4073_: u8 = 0;
    v___x_4073_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_4071_, v_x_4072_);
    return v___x_4073_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_4074_: *mut LeanObject,
    mut v_x_4075_: *mut LeanObject,
    mut v_x_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4077_: u8 = 0;
    let mut v_r_4078_: *mut LeanObject = core::ptr::null_mut();
    v_res_4077_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_4074_, v_x_4075_, v_x_4076_);
    lean_dec_ref(v_x_4076_);
    lean_dec_ref(v_x_4075_);
    v_r_4078_ = lean_box((v_res_4077_) as usize);
    return v_r_4078_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(
    mut v_00_u03b2_4079_: *mut LeanObject,
    mut v_a_4080_: *mut LeanObject,
    mut v_x_4081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    v___x_4082_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_4080_, v_x_4081_);
    return v___x_4082_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(
    mut v_00_u03b2_4083_: *mut LeanObject,
    mut v_a_4084_: *mut LeanObject,
    mut v_x_4085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4086_: *mut LeanObject = core::ptr::null_mut();
    v_res_4086_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_4083_, v_a_4084_, v_x_4085_);
    lean_dec(v_x_4085_);
    lean_dec(v_a_4084_);
    return v_res_4086_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(
    mut v_msgData_4087_: *mut LeanObject,
    mut v_macroStack_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v___x_4092_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_4087_, v_macroStack_4088_, v___y_4090_);
    return v___x_4092_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(
    mut v_msgData_4093_: *mut LeanObject,
    mut v_macroStack_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4098_: *mut LeanObject = core::ptr::null_mut();
    v_res_4098_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(v_msgData_4093_, v_macroStack_4094_, v___y_4095_, v___y_4096_);
    lean_dec(v___y_4096_);
    lean_dec_ref(v___y_4095_);
    return v_res_4098_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(
    mut v_00_u03b2_4099_: *mut LeanObject,
    mut v_x_4100_: *mut LeanObject,
    mut v_x_4101_: usize,
    mut v_x_4102_: *mut LeanObject,
) -> u8 {
    let mut v___x_4103_: u8 = 0;
    v___x_4103_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_4100_, v_x_4101_, v_x_4102_);
    return v___x_4103_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(
    mut v_00_u03b2_4104_: *mut LeanObject,
    mut v_x_4105_: *mut LeanObject,
    mut v_x_4106_: *mut LeanObject,
    mut v_x_4107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_18713__boxed_4108_: usize = 0;
    let mut v_res_4109_: u8 = 0;
    let mut v_r_4110_: *mut LeanObject = core::ptr::null_mut();
    v_x_18713__boxed_4108_ = lean_unbox_usize(v_x_4106_);
    lean_dec(v_x_4106_);
    v_res_4109_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4104_, v_x_4105_, v_x_18713__boxed_4108_, v_x_4107_);
    lean_dec_ref(v_x_4107_);
    lean_dec_ref(v_x_4105_);
    v_r_4110_ = lean_box((v_res_4109_) as usize);
    return v_r_4110_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(
    mut v_00_u03b2_4111_: *mut LeanObject,
    mut v_keys_4112_: *mut LeanObject,
    mut v_vals_4113_: *mut LeanObject,
    mut v_heq_4114_: *mut LeanObject,
    mut v_i_4115_: *mut LeanObject,
    mut v_k_4116_: *mut LeanObject,
) -> u8 {
    let mut v___x_4117_: u8 = 0;
    v___x_4117_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_4112_, v_i_4115_, v_k_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(
    mut v_00_u03b2_4118_: *mut LeanObject,
    mut v_keys_4119_: *mut LeanObject,
    mut v_vals_4120_: *mut LeanObject,
    mut v_heq_4121_: *mut LeanObject,
    mut v_i_4122_: *mut LeanObject,
    mut v_k_4123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4124_: u8 = 0;
    let mut v_r_4125_: *mut LeanObject = core::ptr::null_mut();
    v_res_4124_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(v_00_u03b2_4118_, v_keys_4119_, v_vals_4120_, v_heq_4121_, v_i_4122_, v_k_4123_);
    lean_dec_ref(v_k_4123_);
    lean_dec_ref(v_vals_4120_);
    lean_dec_ref(v_keys_4119_);
    v_r_4125_ = lean_box((v_res_4124_) as usize);
    return v_r_4125_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6() -> *mut LeanObject {
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Array_mkArray0(lean_box(0));
    return v___x_4140_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfOpaque(
    mut v_modifiers_4150_: *mut LeanObject,
    mut v_stx_4151_: *mut LeanObject,
    mut v_a_4152_: *mut LeanObject,
    mut v_a_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v_val_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u8 = 0;
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v_a_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_4225_: u8 = 0;
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v_a_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4251_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4255_: u8 = 0;
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4275_: u8 = 0;
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v_a_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut v_val_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4155_ = lean_unsigned_to_nat(2);
                v___x_4156_ = l_Lean_Syntax_getArg(v_stx_4151_, v___x_4155_);
                v___x_4157_ = l_Lean_Elab_expandDeclSig(v___x_4156_);
                lean_dec(v___x_4156_);
                v_fst_4158_ = lean_ctor_get(v___x_4157_, 0);
                v_snd_4159_ = lean_ctor_get(v___x_4157_, 1);
                v_isSharedCheck_4289_ = (!lean_is_exclusive(v___x_4157_)) as u8;
                if v_isSharedCheck_4289_ == 0 {
                    v___x_4161_ = v___x_4157_;
                    v_isShared_4162_ = v_isSharedCheck_4289_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4159_);
                    lean_inc(v_fst_4158_);
                    lean_dec(v___x_4157_);
                    v___x_4161_ = lean_box(0);
                    v_isShared_4162_ = v_isSharedCheck_4289_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4222_ = lean_unsigned_to_nat(3);
                v___x_4223_ = l_Lean_Syntax_getArg(v_stx_4151_, v___x_4222_);
                v___x_4224_ = l_Lean_Syntax_getOptional_x3f(v___x_4223_);
                lean_dec(v___x_4223_);
                if lean_obj_tag(v___x_4224_) == 0 {
                    v_isUnsafe_4225_ = lean_ctor_get_uint8(
                        v_modifiers_4150_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    if v_isUnsafe_4225_ == 0 {
                        v___x_4226_ = l_Lean_Elab_Command_getRef___redArg(v_a_4152_);
                        if lean_obj_tag(v___x_4226_) == 0 {
                            v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
                            lean_inc(v_a_4227_);
                            lean_dec_ref_known(v___x_4226_, 1);
                            v___x_4228_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_4152_);
                            if lean_obj_tag(v___x_4228_) == 0 {
                                lean_dec_ref_known(v___x_4228_, 1);
                                v_quotContext_x3f_4229_ = lean_ctor_get(v_a_4152_, 5);
                                v___x_4230_ =
                                    l_Lean_SourceInfo_fromRef(v_a_4227_, v_isUnsafe_4225_);
                                lean_dec(v_a_4227_);
                                if lean_obj_tag(v_quotContext_x3f_4229_) == 0 {
                                    v___x_4239_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_4153_);
                                    lean_dec_ref(v___x_4239_);
                                    state = 10;
                                    continue;
                                } else {
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4227_);
                                lean_del_object(v___x_4161_);
                                lean_dec(v_snd_4159_);
                                lean_dec(v_fst_4158_);
                                lean_dec(v_stx_4151_);
                                lean_dec_ref(v_modifiers_4150_);
                                v_a_4240_ = lean_ctor_get(v___x_4228_, 0);
                                v_isSharedCheck_4247_ = (!lean_is_exclusive(v___x_4228_)) as u8;
                                if v_isSharedCheck_4247_ == 0 {
                                    v___x_4242_ = v___x_4228_;
                                    v_isShared_4243_ = v_isSharedCheck_4247_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_4240_);
                                    lean_dec(v___x_4228_);
                                    v___x_4242_ = lean_box(0);
                                    v_isShared_4243_ = v_isSharedCheck_4247_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_4161_);
                            lean_dec(v_snd_4159_);
                            lean_dec(v_fst_4158_);
                            lean_dec(v_stx_4151_);
                            lean_dec_ref(v_modifiers_4150_);
                            v_a_4248_ = lean_ctor_get(v___x_4226_, 0);
                            v_isSharedCheck_4255_ = (!lean_is_exclusive(v___x_4226_)) as u8;
                            if v_isSharedCheck_4255_ == 0 {
                                v___x_4250_ = v___x_4226_;
                                v_isShared_4251_ = v_isSharedCheck_4255_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_4248_);
                                lean_dec(v___x_4226_);
                                v___x_4250_ = lean_box(0);
                                v_isShared_4251_ = v_isSharedCheck_4255_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___x_4256_ = l_Lean_Elab_Command_getRef___redArg(v_a_4152_);
                        if lean_obj_tag(v___x_4256_) == 0 {
                            v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
                            lean_inc(v_a_4257_);
                            lean_dec_ref_known(v___x_4256_, 1);
                            v___x_4258_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_4152_);
                            if lean_obj_tag(v___x_4258_) == 0 {
                                lean_dec_ref_known(v___x_4258_, 1);
                                v_quotContext_x3f_4259_ = lean_ctor_get(v_a_4152_, 5);
                                v___x_4260_ = 0;
                                v___x_4261_ = l_Lean_SourceInfo_fromRef(v_a_4257_, v___x_4260_);
                                lean_dec(v_a_4257_);
                                if lean_obj_tag(v_quotContext_x3f_4259_) == 0 {
                                    v___x_4271_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_4153_);
                                    lean_dec_ref(v___x_4271_);
                                    state = 15;
                                    continue;
                                } else {
                                    state = 15;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4257_);
                                lean_del_object(v___x_4161_);
                                lean_dec(v_snd_4159_);
                                lean_dec(v_fst_4158_);
                                lean_dec(v_stx_4151_);
                                lean_dec_ref(v_modifiers_4150_);
                                v_a_4272_ = lean_ctor_get(v___x_4258_, 0);
                                v_isSharedCheck_4279_ = (!lean_is_exclusive(v___x_4258_)) as u8;
                                if v_isSharedCheck_4279_ == 0 {
                                    v___x_4274_ = v___x_4258_;
                                    v_isShared_4275_ = v_isSharedCheck_4279_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_4272_);
                                    lean_dec(v___x_4258_);
                                    v___x_4274_ = lean_box(0);
                                    v_isShared_4275_ = v_isSharedCheck_4279_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_4161_);
                            lean_dec(v_snd_4159_);
                            lean_dec(v_fst_4158_);
                            lean_dec(v_stx_4151_);
                            lean_dec_ref(v_modifiers_4150_);
                            v_a_4280_ = lean_ctor_get(v___x_4256_, 0);
                            v_isSharedCheck_4287_ = (!lean_is_exclusive(v___x_4256_)) as u8;
                            if v_isSharedCheck_4287_ == 0 {
                                v___x_4282_ = v___x_4256_;
                                v_isShared_4283_ = v_isSharedCheck_4287_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4280_);
                                lean_dec(v___x_4256_);
                                v___x_4282_ = lean_box(0);
                                v_isShared_4283_ = v_isSharedCheck_4287_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4161_);
                    v_val_4288_ = lean_ctor_get(v___x_4224_, 0);
                    lean_inc(v_val_4288_);
                    lean_dec_ref_known(v___x_4224_, 1);
                    v_val_4164_ = v_val_4288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_docString_x3f_4165_ = lean_ctor_get(v_modifiers_4150_, 1);
                lean_inc(v_docString_x3f_4165_);
                v___x_4166_ = 4;
                v___x_4167_ = l_Lean_Syntax_getArgs(v_stx_4151_);
                v___x_4168_ = lean_unsigned_to_nat(3);
                v___x_4169_ = lean_unsigned_to_nat(0);
                v___x_4170_ = l_Array_toSubarray___redArg(v___x_4167_, v___x_4169_, v___x_4168_);
                v___x_4171_ = l_Subarray_copy___redArg(v___x_4170_);
                v___x_4172_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4173_ = lean_box(2);
                v___x_4174_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4174_, 0, v___x_4173_);
                lean_ctor_set(v___x_4174_, 1, v___x_4172_);
                lean_ctor_set(v___x_4174_, 2, v___x_4171_);
                v___x_4175_ = lean_unsigned_to_nat(1);
                v___x_4176_ = l_Lean_Syntax_getArg(v_stx_4151_, v___x_4175_);
                v___x_4177_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4177_, 0, v_snd_4159_);
                v___x_4178_ = lean_box(0);
                v___x_4179_ = lean_alloc_ctor(0, 10, (1) as u32);
                lean_ctor_set(v___x_4179_, 0, v_stx_4151_);
                lean_ctor_set(v___x_4179_, 1, v___x_4174_);
                lean_ctor_set(v___x_4179_, 2, v_modifiers_4150_);
                lean_ctor_set(v___x_4179_, 3, v___x_4176_);
                lean_ctor_set(v___x_4179_, 4, v_fst_4158_);
                lean_ctor_set(v___x_4179_, 5, v___x_4177_);
                lean_ctor_set(v___x_4179_, 6, v_val_4164_);
                lean_ctor_set(v___x_4179_, 7, v_docString_x3f_4165_);
                lean_ctor_set(v___x_4179_, 8, v___x_4178_);
                lean_ctor_set(v___x_4179_, 9, v___x_4178_);
                lean_ctor_set_uint8(
                    v___x_4179_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    v___x_4166_,
                );
                v___x_4180_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4180_, 0, v___x_4179_);
                return v___x_4180_;
            }
            3 => {
                v___x_4184_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1;
                v___x_4185_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2;
                lean_inc(v___y_4183_);
                if v_isShared_4162_ == 0 {
                    lean_ctor_set_tag(v___x_4161_, 2);
                    lean_ctor_set(v___x_4161_, 1, v___x_4185_);
                    lean_ctor_set(v___x_4161_, 0, v___y_4183_);
                    v___x_4187_ = v___x_4161_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4194_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___y_4183_);
                    lean_ctor_set(v_reuseFailAlloc_4194_, 1, v___x_4185_);
                    v___x_4187_ = v_reuseFailAlloc_4194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4188_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5;
                v___x_4189_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4190_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once),
                    _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6,
                );
                lean_inc_n(v___y_4183_, 2);
                v___x_4191_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4191_, 0, v___y_4183_);
                lean_ctor_set(v___x_4191_, 1, v___x_4189_);
                lean_ctor_set(v___x_4191_, 2, v___x_4190_);
                lean_inc_ref_n(v___x_4191_, 2);
                v___x_4192_ =
                    l_Lean_Syntax_node2(v___y_4183_, v___x_4188_, v___x_4191_, v___x_4191_);
                v___x_4193_ = l_Lean_Syntax_node4(
                    v___y_4183_,
                    v___x_4184_,
                    v___x_4187_,
                    v___y_4182_,
                    v___x_4192_,
                    v___x_4191_,
                );
                v_val_4164_ = v___x_4193_;
                state = 2;
                continue;
            }
            5 => {
                v___x_4199_ = l_Lean_Elab_Command_getRef___redArg(v___y_4197_);
                if lean_obj_tag(v___x_4199_) == 0 {
                    v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
                    lean_inc(v_a_4200_);
                    lean_dec_ref_known(v___x_4199_, 1);
                    v___x_4201_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_4197_);
                    if lean_obj_tag(v___x_4201_) == 0 {
                        lean_dec_ref_known(v___x_4201_, 1);
                        v_quotContext_x3f_4202_ = lean_ctor_get(v___y_4197_, 5);
                        v___x_4203_ = 0;
                        v___x_4204_ = l_Lean_SourceInfo_fromRef(v_a_4200_, v___x_4203_);
                        lean_dec(v_a_4200_);
                        if lean_obj_tag(v_quotContext_x3f_4202_) == 0 {
                            v___x_4205_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_4198_);
                            lean_dec_ref(v___x_4205_);
                            v___y_4182_ = v_val_4196_;
                            v___y_4183_ = v___x_4204_;
                            state = 3;
                            continue;
                        } else {
                            v___y_4182_ = v_val_4196_;
                            v___y_4183_ = v___x_4204_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4200_);
                        lean_dec(v_val_4196_);
                        lean_del_object(v___x_4161_);
                        lean_dec(v_snd_4159_);
                        lean_dec(v_fst_4158_);
                        lean_dec(v_stx_4151_);
                        lean_dec_ref(v_modifiers_4150_);
                        v_a_4206_ = lean_ctor_get(v___x_4201_, 0);
                        v_isSharedCheck_4213_ = (!lean_is_exclusive(v___x_4201_)) as u8;
                        if v_isSharedCheck_4213_ == 0 {
                            v___x_4208_ = v___x_4201_;
                            v_isShared_4209_ = v_isSharedCheck_4213_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4206_);
                            lean_dec(v___x_4201_);
                            v___x_4208_ = lean_box(0);
                            v_isShared_4209_ = v_isSharedCheck_4213_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_4196_);
                    lean_del_object(v___x_4161_);
                    lean_dec(v_snd_4159_);
                    lean_dec(v_fst_4158_);
                    lean_dec(v_stx_4151_);
                    lean_dec_ref(v_modifiers_4150_);
                    v_a_4214_ = lean_ctor_get(v___x_4199_, 0);
                    v_isSharedCheck_4221_ = (!lean_is_exclusive(v___x_4199_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4216_ = v___x_4199_;
                        v_isShared_4217_ = v_isSharedCheck_4221_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4214_);
                        lean_dec(v___x_4199_);
                        v___x_4216_ = lean_box(0);
                        v_isShared_4217_ = v_isSharedCheck_4221_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4209_ == 0 {
                    v___x_4211_ = v___x_4208_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
                    v___x_4211_ = v_reuseFailAlloc_4212_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4211_;
            }
            8 => {
                if v_isShared_4217_ == 0 {
                    v___x_4219_ = v___x_4216_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
                    v___x_4219_ = v_reuseFailAlloc_4220_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4219_;
            }
            10 => {
                v___x_4232_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9;
                v___x_4233_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10;
                lean_inc_n(v___x_4230_, 2);
                v___x_4234_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4234_, 0, v___x_4230_);
                lean_ctor_set(v___x_4234_, 1, v___x_4233_);
                v___x_4235_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4236_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once),
                    _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6,
                );
                v___x_4237_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4237_, 0, v___x_4230_);
                lean_ctor_set(v___x_4237_, 1, v___x_4235_);
                lean_ctor_set(v___x_4237_, 2, v___x_4236_);
                v___x_4238_ =
                    l_Lean_Syntax_node2(v___x_4230_, v___x_4232_, v___x_4234_, v___x_4237_);
                v_val_4196_ = v___x_4238_;
                v___y_4197_ = v_a_4152_;
                v___y_4198_ = v_a_4153_;
                state = 5;
                continue;
            }
            11 => {
                if v_isShared_4243_ == 0 {
                    v___x_4245_ = v___x_4242_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4245_;
            }
            13 => {
                if v_isShared_4251_ == 0 {
                    v___x_4253_ = v___x_4250_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
                    v___x_4253_ = v_reuseFailAlloc_4254_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4253_;
            }
            15 => {
                v___x_4263_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9;
                v___x_4264_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10;
                lean_inc_n(v___x_4261_, 3);
                v___x_4265_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4265_, 0, v___x_4261_);
                lean_ctor_set(v___x_4265_, 1, v___x_4264_);
                v___x_4266_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4267_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11;
                v___x_4268_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4268_, 0, v___x_4261_);
                lean_ctor_set(v___x_4268_, 1, v___x_4267_);
                v___x_4269_ = l_Lean_Syntax_node1(v___x_4261_, v___x_4266_, v___x_4268_);
                v___x_4270_ =
                    l_Lean_Syntax_node2(v___x_4261_, v___x_4263_, v___x_4265_, v___x_4269_);
                v_val_4196_ = v___x_4270_;
                v___y_4197_ = v_a_4152_;
                v___y_4198_ = v_a_4153_;
                state = 5;
                continue;
            }
            16 => {
                if v_isShared_4275_ == 0 {
                    v___x_4277_ = v___x_4274_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
                    v___x_4277_ = v_reuseFailAlloc_4278_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4277_;
            }
            18 => {
                if v_isShared_4283_ == 0 {
                    v___x_4285_ = v___x_4282_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
                    v___x_4285_ = v_reuseFailAlloc_4286_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(
    mut v_modifiers_4290_: *mut LeanObject,
    mut v_stx_4291_: *mut LeanObject,
    mut v_a_4292_: *mut LeanObject,
    mut v_a_4293_: *mut LeanObject,
    mut v_a_4294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4295_: *mut LeanObject = core::ptr::null_mut();
    v_res_4295_ =
        l_Lean_Elab_Command_mkDefViewOfOpaque(v_modifiers_4290_, v_stx_4291_, v_a_4292_, v_a_4293_);
    lean_dec(v_a_4293_);
    lean_dec_ref(v_a_4292_);
    return v_res_4295_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfExample(
    mut v_modifiers_4308_: *mut LeanObject,
    mut v_stx_4309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: u8 = 0;
    let mut v_id_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: u8 = 0;
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    v___x_4310_ = lean_unsigned_to_nat(1);
    v___x_4311_ = l_Lean_Syntax_getArg(v_stx_4309_, v___x_4310_);
    v___x_4312_ = l_Lean_Elab_expandOptDeclSig(v___x_4311_);
    lean_dec(v___x_4311_);
    v_fst_4313_ = lean_ctor_get(v___x_4312_, 0);
    lean_inc(v_fst_4313_);
    v_snd_4314_ = lean_ctor_get(v___x_4312_, 1);
    lean_inc(v_snd_4314_);
    lean_dec_ref(v___x_4312_);
    v___x_4315_ = lean_unsigned_to_nat(0);
    v___x_4316_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
    v___x_4317_ = lean_box(2);
    v___x_4318_ = l_Lean_Elab_Command_mkDefViewOfExample___closed__0;
    v_docString_x3f_4319_ = lean_ctor_get(v_modifiers_4308_, 1);
    lean_inc(v_docString_x3f_4319_);
    v___x_4320_ = l_Lean_Syntax_getArg(v_stx_4309_, v___x_4315_);
    v___x_4321_ = l_Lean_Elab_Command_mkDefViewOfExample___closed__2;
    v___x_4322_ = 1;
    v_id_4323_ = l_Lean_mkIdentFrom(v___x_4320_, v___x_4321_, v___x_4322_);
    lean_dec(v___x_4320_);
    v___x_4324_ = l_Lean_Elab_Command_mkDefViewOfExample___closed__3;
    v___x_4325_ = lean_unsigned_to_nat(2);
    v___x_4326_ = lean_mk_empty_array_with_capacity(v___x_4325_);
    v___x_4327_ = lean_array_push(v___x_4326_, v_id_4323_);
    v___x_4328_ = lean_array_push(v___x_4327_, v___x_4318_);
    v___x_4329_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_4329_, 0, v___x_4317_);
    lean_ctor_set(v___x_4329_, 1, v___x_4324_);
    lean_ctor_set(v___x_4329_, 2, v___x_4328_);
    v___x_4330_ = 3;
    v___x_4331_ = l_Lean_Syntax_getArgs(v_stx_4309_);
    v___x_4332_ = l_Array_toSubarray___redArg(v___x_4331_, v___x_4315_, v___x_4325_);
    v___x_4333_ = l_Subarray_copy___redArg(v___x_4332_);
    v___x_4334_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_4334_, 0, v___x_4317_);
    lean_ctor_set(v___x_4334_, 1, v___x_4316_);
    lean_ctor_set(v___x_4334_, 2, v___x_4333_);
    v___x_4335_ = l_Lean_Syntax_getArg(v_stx_4309_, v___x_4325_);
    v___x_4336_ = lean_box(0);
    v___x_4337_ = lean_alloc_ctor(0, 10, (1) as u32);
    lean_ctor_set(v___x_4337_, 0, v_stx_4309_);
    lean_ctor_set(v___x_4337_, 1, v___x_4334_);
    lean_ctor_set(v___x_4337_, 2, v_modifiers_4308_);
    lean_ctor_set(v___x_4337_, 3, v___x_4329_);
    lean_ctor_set(v___x_4337_, 4, v_fst_4313_);
    lean_ctor_set(v___x_4337_, 5, v_snd_4314_);
    lean_ctor_set(v___x_4337_, 6, v___x_4335_);
    lean_ctor_set(v___x_4337_, 7, v_docString_x3f_4319_);
    lean_ctor_set(v___x_4337_, 8, v___x_4336_);
    lean_ctor_set(v___x_4337_, 9, v___x_4336_);
    lean_ctor_set_uint8(
        v___x_4337_,
        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
        v___x_4330_,
    );
    return v___x_4337_;
}
pub unsafe fn l_Lean_Elab_Command_isDefLike(mut v_stx_4373_: *mut LeanObject) -> u8 {
    let mut v_declKind_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4376_: u8 = 0;
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: u8 = 0;
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declKind_4374_ = l_Lean_Syntax_getKind(v_stx_4373_);
                v___x_4385_ = l_Lean_Elab_Command_isDefLike___closed__8;
                v___x_4386_ = lean_name_eq(v_declKind_4374_, v___x_4385_);
                if v___x_4386_ == 0 {
                    v___x_4387_ = l_Lean_Elab_Command_isDefLike___closed__10;
                    v___x_4388_ = lean_name_eq(v_declKind_4374_, v___x_4387_);
                    v___y_4376_ = v___x_4388_;
                    state = 1;
                    continue;
                } else {
                    v___y_4376_ = v___x_4386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4376_ == 0 {
                    v___x_4377_ = l_Lean_Elab_Command_isDefLike___closed__1;
                    v___x_4378_ = lean_name_eq(v_declKind_4374_, v___x_4377_);
                    if v___x_4378_ == 0 {
                        v___x_4379_ = l_Lean_Elab_Command_isDefLike___closed__3;
                        v___x_4380_ = lean_name_eq(v_declKind_4374_, v___x_4379_);
                        if v___x_4380_ == 0 {
                            v___x_4381_ = l_Lean_Elab_Command_isDefLike___closed__4;
                            v___x_4382_ = lean_name_eq(v_declKind_4374_, v___x_4381_);
                            if v___x_4382_ == 0 {
                                v___x_4383_ = l_Lean_Elab_Command_isDefLike___closed__6;
                                v___x_4384_ = lean_name_eq(v_declKind_4374_, v___x_4383_);
                                lean_dec(v_declKind_4374_);
                                return v___x_4384_;
                            } else {
                                lean_dec(v_declKind_4374_);
                                return v___x_4382_;
                            }
                        } else {
                            lean_dec(v_declKind_4374_);
                            return v___x_4380_;
                        }
                    } else {
                        lean_dec(v_declKind_4374_);
                        return v___x_4378_;
                    }
                } else {
                    lean_dec(v_declKind_4374_);
                    return v___y_4376_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_isDefLike___boxed(
    mut v_stx_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4390_: u8 = 0;
    let mut v_r_4391_: *mut LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_Lean_Elab_Command_isDefLike(v_stx_4389_);
    v_r_4391_ = lean_box((v_res_4390_) as usize);
    return v_r_4391_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefView___closed__1() -> *mut LeanObject {
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lean_Elab_Command_mkDefView___closed__0;
    v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefView(
    mut v_modifiers_4395_: *mut LeanObject,
    mut v_stx_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
    mut v_a_4398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v_stx_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visibility_4407_: u8 = 0;
    let mut v_isProtected_4408_: u8 = 0;
    let mut v_computeKind_4409_: u8 = 0;
    let mut v_recKind_4410_: u8 = 0;
    let mut v_isUnsafe_4411_: u8 = 0;
    let mut v_attrs_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declKind_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: u8 = 0;
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: u8 = 0;
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u8 = 0;
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: u8 = 0;
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4449_: u8 = 0;
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u8 = 0;
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: u8 = 0;
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4461_: u8 = 0;
    let mut v_unused_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: u8 = 0;
    let mut v_isMeta_4467_: u8 = 0;
    let mut v_isSharedCheck_4468_: u8 = 0;
    let mut v_a_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4400_ = l_Lean_Elab_Command_getScope___redArg(v_a_4398_);
                if lean_obj_tag(v___x_4400_) == 0 {
                    v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
                    v_isSharedCheck_4468_ = (!lean_is_exclusive(v___x_4400_)) as u8;
                    if v_isSharedCheck_4468_ == 0 {
                        v___x_4403_ = v___x_4400_;
                        v_isShared_4404_ = v_isSharedCheck_4468_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4401_);
                        lean_dec(v___x_4400_);
                        v___x_4403_ = lean_box(0);
                        v_isShared_4404_ = v_isSharedCheck_4468_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_4396_);
                    lean_dec_ref(v_modifiers_4395_);
                    v_a_4469_ = lean_ctor_get(v___x_4400_, 0);
                    v_isSharedCheck_4476_ = (!lean_is_exclusive(v___x_4400_)) as u8;
                    if v_isSharedCheck_4476_ == 0 {
                        v___x_4471_ = v___x_4400_;
                        v_isShared_4472_ = v_isSharedCheck_4476_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4469_);
                        lean_dec(v___x_4400_);
                        v___x_4471_ = lean_box(0);
                        v_isShared_4472_ = v_isSharedCheck_4476_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_4405_ = lean_ctor_get(v_modifiers_4395_, 0);
                v_docString_x3f_4406_ = lean_ctor_get(v_modifiers_4395_, 1);
                v_visibility_4407_ = lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isProtected_4408_ = lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_computeKind_4409_ = lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_recKind_4410_ = lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_isUnsafe_4411_ = lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_attrs_4412_ = lean_ctor_get(v_modifiers_4395_, 2);
                lean_inc(v_stx_4396_);
                v_declKind_4413_ = l_Lean_Syntax_getKind(v_stx_4396_);
                v___x_4465_ = 0;
                v___x_4466_ = l_Lean_Elab_instBEqComputeKind_beq(v_computeKind_4409_, v___x_4465_);
                if v___x_4466_ == 0 {
                    lean_dec(v_a_4401_);
                    v___y_4449_ = v___x_4466_;
                    state = 7;
                    continue;
                } else {
                    v_isMeta_4467_ = lean_ctor_get_uint8(
                        v_a_4401_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                    );
                    lean_dec(v_a_4401_);
                    v___y_4449_ = v_isMeta_4467_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v___x_4416_ = l_Lean_Elab_Command_isDefLike___closed__8;
                v___x_4417_ = lean_name_eq(v_declKind_4413_, v___x_4416_);
                if v___x_4417_ == 0 {
                    v___x_4418_ = l_Lean_Elab_Command_isDefLike___closed__10;
                    v___x_4419_ = lean_name_eq(v_declKind_4413_, v___x_4418_);
                    if v___x_4419_ == 0 {
                        v___x_4420_ = l_Lean_Elab_Command_isDefLike___closed__1;
                        v___x_4421_ = lean_name_eq(v_declKind_4413_, v___x_4420_);
                        if v___x_4421_ == 0 {
                            v___x_4422_ = l_Lean_Elab_Command_isDefLike___closed__3;
                            v___x_4423_ = lean_name_eq(v_declKind_4413_, v___x_4422_);
                            if v___x_4423_ == 0 {
                                v___x_4424_ = l_Lean_Elab_Command_isDefLike___closed__4;
                                v___x_4425_ = lean_name_eq(v_declKind_4413_, v___x_4424_);
                                if v___x_4425_ == 0 {
                                    v___x_4426_ = l_Lean_Elab_Command_isDefLike___closed__6;
                                    v___x_4427_ = lean_name_eq(v_declKind_4413_, v___x_4426_);
                                    lean_dec(v_declKind_4413_);
                                    if v___x_4427_ == 0 {
                                        lean_dec_ref(v___y_4415_);
                                        lean_del_object(v___x_4403_);
                                        lean_dec(v_stx_4396_);
                                        v___x_4428_ = lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Command_mkDefView___closed__1
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Command_mkDefView___closed__1_once
                                            ),
                                            _init_l_Lean_Elab_Command_mkDefView___closed__1,
                                        );
                                        v___x_4429_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v___x_4428_, v_a_4397_, v_a_4398_);
                                        return v___x_4429_;
                                    } else {
                                        v___x_4430_ = l_Lean_Elab_Command_mkDefViewOfExample(
                                            v___y_4415_,
                                            v_stx_4396_,
                                        );
                                        if v_isShared_4404_ == 0 {
                                            lean_ctor_set(v___x_4403_, 0, v___x_4430_);
                                            v___x_4432_ = v___x_4403_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4433_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4430_);
                                            v___x_4432_ = v_reuseFailAlloc_4433_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_declKind_4413_);
                                    lean_del_object(v___x_4403_);
                                    v___x_4434_ = l_Lean_Elab_Command_mkDefViewOfInstance(
                                        v___y_4415_,
                                        v_stx_4396_,
                                        v_a_4397_,
                                        v_a_4398_,
                                    );
                                    return v___x_4434_;
                                }
                            } else {
                                lean_dec(v_declKind_4413_);
                                lean_del_object(v___x_4403_);
                                v___x_4435_ = l_Lean_Elab_Command_mkDefViewOfOpaque(
                                    v___y_4415_,
                                    v_stx_4396_,
                                    v_a_4397_,
                                    v_a_4398_,
                                );
                                return v___x_4435_;
                            }
                        } else {
                            lean_dec(v_declKind_4413_);
                            v___x_4436_ =
                                l_Lean_Elab_Command_mkDefViewOfTheorem(v___y_4415_, v_stx_4396_);
                            if v_isShared_4404_ == 0 {
                                lean_ctor_set(v___x_4403_, 0, v___x_4436_);
                                v___x_4438_ = v___x_4403_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
                                v___x_4438_ = v_reuseFailAlloc_4439_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_declKind_4413_);
                        v___x_4440_ = l_Lean_Elab_Command_mkDefViewOfDef(v___y_4415_, v_stx_4396_);
                        if v_isShared_4404_ == 0 {
                            lean_ctor_set(v___x_4403_, 0, v___x_4440_);
                            v___x_4442_ = v___x_4403_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
                            v___x_4442_ = v_reuseFailAlloc_4443_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declKind_4413_);
                    v___x_4444_ = l_Lean_Elab_Command_mkDefViewOfAbbrev(v___y_4415_, v_stx_4396_);
                    if v_isShared_4404_ == 0 {
                        lean_ctor_set(v___x_4403_, 0, v___x_4444_);
                        v___x_4446_ = v___x_4403_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
                        v___x_4446_ = v_reuseFailAlloc_4447_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4432_;
            }
            4 => {
                return v___x_4438_;
            }
            5 => {
                return v___x_4442_;
            }
            6 => {
                return v___x_4446_;
            }
            7 => {
                if v___y_4449_ == 0 {
                    v___y_4415_ = v_modifiers_4395_;
                    state = 2;
                    continue;
                } else {
                    v___x_4450_ = l_Lean_Elab_Command_isDefLike___closed__1;
                    v___x_4451_ = lean_name_eq(v_declKind_4413_, v___x_4450_);
                    if v___x_4451_ == 0 {
                        v___x_4452_ = l_Lean_Elab_Command_isDefLike___closed__6;
                        v___x_4453_ = lean_name_eq(v_declKind_4413_, v___x_4452_);
                        if v___x_4453_ == 0 {
                            lean_inc_ref(v_attrs_4412_);
                            lean_inc(v_docString_x3f_4406_);
                            lean_inc(v_stx_4405_);
                            v_isSharedCheck_4461_ = (!lean_is_exclusive(v_modifiers_4395_)) as u8;
                            if v_isSharedCheck_4461_ == 0 {
                                v_unused_4462_ = lean_ctor_get(v_modifiers_4395_, 2);
                                lean_dec(v_unused_4462_);
                                v_unused_4463_ = lean_ctor_get(v_modifiers_4395_, 1);
                                lean_dec(v_unused_4463_);
                                v_unused_4464_ = lean_ctor_get(v_modifiers_4395_, 0);
                                lean_dec(v_unused_4464_);
                                v___x_4455_ = v_modifiers_4395_;
                                v_isShared_4456_ = v_isSharedCheck_4461_;
                                state = 8;
                                continue;
                            } else {
                                lean_dec(v_modifiers_4395_);
                                v___x_4455_ = lean_box(0);
                                v_isShared_4456_ = v_isSharedCheck_4461_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___y_4415_ = v_modifiers_4395_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_4415_ = v_modifiers_4395_;
                        state = 2;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4457_ = 1;
                if v_isShared_4456_ == 0 {
                    v___x_4459_ = v___x_4455_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_stx_4405_);
                    lean_ctor_set(v_reuseFailAlloc_4460_, 1, v_docString_x3f_4406_);
                    lean_ctor_set(v_reuseFailAlloc_4460_, 2, v_attrs_4412_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_visibility_4407_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isProtected_4408_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_recKind_4410_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_isUnsafe_4411_,
                    );
                    v___x_4459_ = v_reuseFailAlloc_4460_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_ctor_set_uint8(
                    v___x_4459_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v___x_4457_,
                );
                v___y_4415_ = v___x_4459_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_4472_ == 0 {
                    v___x_4474_ = v___x_4471_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
                    v___x_4474_ = v_reuseFailAlloc_4475_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefView___boxed(
    mut v_modifiers_4477_: *mut LeanObject,
    mut v_stx_4478_: *mut LeanObject,
    mut v_a_4479_: *mut LeanObject,
    mut v_a_4480_: *mut LeanObject,
    mut v_a_4481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4482_: *mut LeanObject = core::ptr::null_mut();
    v_res_4482_ =
        l_Lean_Elab_Command_mkDefView(v_modifiers_4477_, v_stx_4478_, v_a_4479_, v_a_4480_);
    lean_dec(v_a_4480_);
    lean_dec_ref(v_a_4479_);
    return v_res_4482_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    v___x_4544_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4545_ = 0;
    v___x_4546_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4547_ = l_Lean_registerTraceClass(v___x_4544_, v___x_4545_, v___x_4546_);
    return v___x_4547_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(
    mut v_a_4548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4549_: *mut LeanObject = core::ptr::null_mut();
    v_res_4549_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
    return v_res_4549_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    v___x_4550_ = lean_unsigned_to_nat(2390142386);
    v___x_4551_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4552_ = l_Lean_Name_num___override(v___x_4551_, v___x_4550_);
    return v___x_4552_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    v___x_4553_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4554_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4555_ = l_Lean_Name_str___override(v___x_4554_, v___x_4553_);
    return v___x_4555_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    v___x_4556_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4557_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4558_ = l_Lean_Name_str___override(v___x_4557_, v___x_4556_);
    return v___x_4558_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    v___x_4559_ = lean_unsigned_to_nat(2);
    v___x_4560_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4561_ = l_Lean_Name_num___override(v___x_4560_, v___x_4559_);
    return v___x_4561_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    v___x_4563_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
    v___x_4564_ = 0;
    v___x_4565_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4566_ = l_Lean_registerTraceClass(v___x_4563_, v___x_4564_, v___x_4565_);
    return v___x_4566_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(
    mut v_a_4567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4568_: *mut LeanObject = core::ptr::null_mut();
    v_res_4568_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
    return v_res_4568_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DefView(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_instInhabitedDefKind_default = _init_l_Lean_Elab_instInhabitedDefKind_default();
    l_Lean_Elab_instInhabitedDefKind = _init_l_Lean_Elab_instInhabitedDefKind();
    l_Lean_Elab_instInhabitedDefViewElabHeaderData_default =
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default();
    lean_mark_persistent(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default);
    l_Lean_Elab_instInhabitedDefViewElabHeaderData =
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData();
    lean_mark_persistent(l_Lean_Elab_instInhabitedDefViewElabHeaderData);
    l_Lean_Elab_instInhabitedDefView_default = _init_l_Lean_Elab_instInhabitedDefView_default();
    lean_mark_persistent(l_Lean_Elab_instInhabitedDefView_default);
    l_Lean_Elab_instInhabitedDefView = _init_l_Lean_Elab_instInhabitedDefView();
    lean_mark_persistent(l_Lean_Elab_instInhabitedDefView);
    res = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DefView(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DefView(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_DeclNameGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DefView(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DefView(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_DefView(builtin);
}
