// Lean compiler output
// Module: Lean.Elab.BinderPredicates
// Imports: Lean.Elab.MacroArgUtil Lean.Linter.MissingDocs
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_unzip___redArg};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit, l_Lean_evalOptPrio___boxed,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_addMacroScope,
    l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_elabCommand,
    l_Lean_Elab_Command_getCurrMacroScope___redArg, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::MacroArgUtil::{
    initialize_Lean_Elab_MacroArgUtil, l_Lean_Elab_Command_expandMacroArg,
    runtime_initialize_Lean_Elab_MacroArgUtil,
};
use crate::r#gen::Lean::Elab::Syntax::l_Lean_Elab_Command_elabSyntax;
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_expandMacroImpl_x3f, l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Linter::MissingDocs::{
    initialize_Lean_Linter_MissingDocs, l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed,
    l_Lean_Linter_MissingDocs_addBuiltinHandler, l_Lean_Linter_MissingDocs_lint,
    l_Lean_Linter_MissingDocs_lintNamed, runtime_initialize_Lean_Linter_MissingDocs,
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
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
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
    lean_nat_add, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
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
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__2_value) as *mut LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__0_value) as *mut LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__1_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__3_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__11_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__13_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__15_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__18_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__18_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___closed__0_value: LeanStringObject<158> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Command_elabBinderPred___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__2_value: LeanStringObject<10> =
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
        m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__3_value: LeanStringObject<9> =
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
        m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__4_value: LeanStringObject<2> =
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
        m_data: [124, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__5_value: LeanStringObject<5> =
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
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__6_value: LeanStringObject<3> =
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
        m_data: [96, 40, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__7_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            116, 101, 114, 109, 83, 97, 116, 105, 115, 102, 105, 101, 115, 95, 98, 105, 110, 100,
            101, 114, 95, 112, 114, 101, 100, 37, 95, 95, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__7_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__7_value)
                as *mut LeanObject,
            5900987525369307171 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__9_value: LeanStringObject<23> =
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
            115, 97, 116, 105, 115, 102, 105, 101, 115, 95, 98, 105, 110, 100, 101, 114, 95, 112,
            114, 101, 100, 37, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__10_value: LeanStringObject<7> =
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
        m_data: [112, 115, 101, 117, 100, 111, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__10_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__11_value: LeanStringObject<9> =
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
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__11_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__12_value: LeanStringObject<2> =
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
        m_data: [36, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__12_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__13_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            97, 110, 116, 105, 113, 117, 111, 116, 78, 101, 115, 116, 101, 100, 69, 120, 112, 114,
            0,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__13_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__13_value)
                as *mut LeanObject,
            9054665995413608708 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__14_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__15_value: LeanStringObject<13> =
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
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__15_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__15_value)
                as *mut LeanObject,
            5763156871072657475 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__16_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__17_value: LeanStringObject<3> =
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
        m_data: [61, 62, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__17_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__18_value: LeanStringObject<8> =
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
static mut l_Lean_Elab_Command_elabBinderPred___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__19_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 105, 99, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__19_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__20_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__20_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__20_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__20_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__20_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__20_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__19_value)
                as *mut LeanObject,
            3436363153240052362 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__20_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__21_value: LeanStringObject<12> =
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
        m_data: [109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__21_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__22_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__22_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__22_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__22_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__22_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__22_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__21_value)
                as *mut LeanObject,
            127604530719969405 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__22_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__23_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Command_elabBinderPred___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__23_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__24_value: LeanStringObject<10> =
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
        m_data: [110, 97, 109, 101, 100, 80, 114, 105, 111, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__24_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__25_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__25_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__25_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__25_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__25_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__25_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__25_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__24_value)
                as *mut LeanObject,
            13348752267415789739 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__25_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__26_value: LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__26_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__27_value: LeanStringObject<9> =
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
        m_data: [112, 114, 105, 111, 114, 105, 116, 121, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__27_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__28_value: LeanStringObject<3> =
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
static mut l_Lean_Elab_Command_elabBinderPred___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__28_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__29_value: LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__29_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__30_value: LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__30_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__31_value: LeanStringObject<11> =
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
        m_data: [98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__31_value) as *mut LeanObject;
static mut l_Lean_Elab_Command_elabBinderPred___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabBinderPred___closed__32: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabBinderPred___closed__33_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__31_value)
                as *mut LeanObject,
            13780673489923901146 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__33_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__34_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__34_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__34_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__31_value)
                as *mut LeanObject,
            5871181422166457019 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__34_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__35_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__34_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__35_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__36_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__35_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__36_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__37_value: LeanStringObject<10> =
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
        m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__37_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__38_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__38_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__38_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__38_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__38_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__38_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__38_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__37_value)
                as *mut LeanObject,
            17682753938374962505 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__38_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__39_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__39_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__40_value: LeanStringObject<11> =
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
        m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__40_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__41_value: LeanStringObject<3> =
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
        m_data: [64, 91, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__41_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__42_value: LeanStringObject<2> =
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
static mut l_Lean_Elab_Command_elabBinderPred___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__42_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__43_value: LeanStringObject<7> =
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
        m_data: [115, 121, 110, 116, 97, 120, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__43_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__44_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__44_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__44_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__44_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__44_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__44_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__44_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__43_value)
                as *mut LeanObject,
            2812521669163367463 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__44_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__45_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_elabBinderPred___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__45_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__46_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__45_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__46_value) as *mut LeanObject;
static mut l_Lean_Elab_Command_elabBinderPred___closed__47_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabBinderPred___closed__47: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabBinderPred___closed__48_value: LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__48_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__49_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_elabBinderPred___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__49_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__50_value: LeanStringObject<9> =
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
        m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__50_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__51_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__51_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__51_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__51_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__51_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__49_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__51_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__51_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__50_value)
                as *mut LeanObject,
            7983999284776576032 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__51_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__52_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__52_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__52_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__52_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__52_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__49_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__52_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__52_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__40_value)
                as *mut LeanObject,
            2533412339571800130 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__52_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabBinderPred___closed__53_value: LeanStringObject<11> =
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
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__53_value) as *mut LeanObject;
static l_Lean_Elab_Command_elabBinderPred___closed__54_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__54_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__54_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabBinderPred___closed__54_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__54_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabBinderPred___closed__54_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__54_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__53_value)
                as *mut LeanObject,
            9063780239635860524 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabBinderPred___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__54_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__1_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 66, 105, 110, 100, 101, 114, 80, 114, 101, 100, 0]};
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__18_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__1_value) as *mut LeanObject,16989956371562340279 as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 40 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 33 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__0_value) as *mut LeanObject,((( 40 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__3_value) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__4_value) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_checkBinderPredicate___closed__0_value: LeanStringObject<17> =
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
            98, 105, 110, 100, 101, 114, 32, 112, 114, 101, 100, 105, 99, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_checkBinderPredicate___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_checkBinderPredicate___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_checkBinderPredicate___closed__1_value: LeanStringObject<6> =
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
        m_data: [108, 111, 99, 97, 108, 0],
    };
static mut l_Lean_Elab_Command_checkBinderPredicate___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_checkBinderPredicate___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_checkBinderPredicate___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_checkBinderPredicate___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_checkBinderPredicate___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_checkBinderPredicate___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_checkBinderPredicate___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabBinderPred___closed__49_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_checkBinderPredicate___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_checkBinderPredicate___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_checkBinderPredicate___closed__1_value)
                as *mut LeanObject,
            312453245906544776 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_checkBinderPredicate___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_checkBinderPredicate___closed__2_value)
        as *mut LeanObject;
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = lean_box(0);
    v___x_1826_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1827_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1827_, 0, v___x_1826_);
    lean_ctor_set(v___x_1827_, 1, v___x_1825_);
    return v___x_1827_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    v___x_1829_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg___closed__0);
    v___x_1830_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1830_, 0, v___x_1829_);
    return v___x_1830_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg___boxed(
    mut v___y_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1832_: *mut LeanObject = core::ptr::null_mut();
    v_res_1832_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
    return v_res_1832_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0(
    mut v_00_u03b1_1833_: *mut LeanObject,
    mut v___y_1834_: *mut LeanObject,
    mut v___y_1835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    v___x_1837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
    return v___x_1837_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___boxed(
    mut v_00_u03b1_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1842_: *mut LeanObject = core::ptr::null_mut();
    v_res_1842_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0(
            v_00_u03b1_1838_,
            v___y_1839_,
            v___y_1840_,
        );
    lean_dec(v___y_1840_);
    lean_dec_ref(v___y_1839_);
    return v_res_1842_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___redArg(
    mut v___y_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    v___x_1845_ = lean_st_ref_get(v___y_1843_);
    v_env_1846_ = lean_ctor_get(v___x_1845_, 0);
    lean_inc_ref(v_env_1846_);
    lean_dec(v___x_1845_);
    v___x_1847_ = l_Lean_Environment_header(v_env_1846_);
    lean_dec_ref(v_env_1846_);
    v_mainModule_1848_ = lean_ctor_get(v___x_1847_, 0);
    lean_inc(v_mainModule_1848_);
    lean_dec_ref(v___x_1847_);
    v___x_1849_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1849_, 0, v_mainModule_1848_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___redArg___boxed(
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1852_: *mut LeanObject = core::ptr::null_mut();
    v_res_1852_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___redArg(
        v___y_1850_,
    );
    lean_dec(v___y_1850_);
    return v_res_1852_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4(
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    v___x_1856_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___redArg(
        v___y_1854_,
    );
    return v___x_1856_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___boxed(
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1860_: *mut LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4(
        v___y_1857_,
        v___y_1858_,
    );
    lean_dec(v___y_1858_);
    lean_dec_ref(v___y_1857_);
    return v_res_1860_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__3(
    mut v_sz_1861_: usize,
    mut v_i_1862_: usize,
    mut v_bs_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1864_: u8 = 0;
    let mut v_v_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: usize = 0;
    let mut v___x_1869_: usize = 0;
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1864_ = lean_usize_dec_lt(v_i_1862_, v_sz_1861_);
                if v___x_1864_ == 0 {
                    return v_bs_1863_;
                } else {
                    v_v_1865_ = lean_array_uget(v_bs_1863_, v_i_1862_);
                    v___x_1866_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1867_ = lean_array_uset(v_bs_1863_, v_i_1862_, v___x_1866_);
                    v___x_1868_ = 1usize;
                    v___x_1869_ = lean_usize_add(v_i_1862_, v___x_1868_);
                    v___x_1870_ = lean_array_uset(v_bs_x27_1867_, v_i_1862_, v_v_1865_);
                    v_i_1862_ = v___x_1869_;
                    v_bs_1863_ = v___x_1870_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__3___boxed(
    mut v_sz_1872_: *mut LeanObject,
    mut v_i_1873_: *mut LeanObject,
    mut v_bs_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1875_: usize = 0;
    let mut v_i_boxed_1876_: usize = 0;
    let mut v_res_1877_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1875_ = lean_unbox_usize(v_sz_1872_);
    lean_dec(v_sz_1872_);
    v_i_boxed_1876_ = lean_unbox_usize(v_i_1873_);
    lean_dec(v_i_1873_);
    v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__3(v_sz_boxed_1875_, v_i_boxed_1876_, v_bs_1874_);
    return v_res_1877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__2(
    mut v_sz_1878_: usize,
    mut v_i_1879_: usize,
    mut v_bs_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1884_: u8 = 0;
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: usize = 0;
    let mut v___x_1892_: usize = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1884_ = lean_usize_dec_lt(v_i_1879_, v_sz_1878_);
                if v___x_1884_ == 0 {
                    v___x_1885_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1885_, 0, v_bs_1880_);
                    return v___x_1885_;
                } else {
                    v_v_1886_ = lean_array_uget_borrowed(v_bs_1880_, v_i_1879_);
                    lean_inc(v_v_1886_);
                    v___x_1887_ =
                        l_Lean_Elab_Command_expandMacroArg(v_v_1886_, v___y_1881_, v___y_1882_);
                    if lean_obj_tag(v___x_1887_) == 0 {
                        v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
                        lean_inc(v_a_1888_);
                        lean_dec_ref_known(v___x_1887_, 1);
                        v___x_1889_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1890_ = lean_array_uset(v_bs_1880_, v_i_1879_, v___x_1889_);
                        v___x_1891_ = 1usize;
                        v___x_1892_ = lean_usize_add(v_i_1879_, v___x_1891_);
                        v___x_1893_ = lean_array_uset(v_bs_x27_1890_, v_i_1879_, v_a_1888_);
                        v_i_1879_ = v___x_1892_;
                        v_bs_1880_ = v___x_1893_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_1880_);
                        v_a_1895_ = lean_ctor_get(v___x_1887_, 0);
                        v_isSharedCheck_1902_ = (!lean_is_exclusive(v___x_1887_)) as u8;
                        if v_isSharedCheck_1902_ == 0 {
                            v___x_1897_ = v___x_1887_;
                            v_isShared_1898_ = v_isSharedCheck_1902_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1895_);
                            lean_dec(v___x_1887_);
                            v___x_1897_ = lean_box(0);
                            v_isShared_1898_ = v_isSharedCheck_1902_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1898_ == 0 {
                    v___x_1900_ = v___x_1897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
                    v___x_1900_ = v_reuseFailAlloc_1901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__2___boxed(
    mut v_sz_1903_: *mut LeanObject,
    mut v_i_1904_: *mut LeanObject,
    mut v_bs_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1909_: usize = 0;
    let mut v_i_boxed_1910_: usize = 0;
    let mut v_res_1911_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1909_ = lean_unbox_usize(v_sz_1903_);
    lean_dec(v_sz_1903_);
    v_i_boxed_1910_ = lean_unbox_usize(v_i_1904_);
    lean_dec(v_i_1904_);
    v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__2(v_sz_boxed_1909_, v_i_boxed_1910_, v_bs_1905_, v___y_1906_, v___y_1907_);
    lean_dec(v___y_1907_);
    lean_dec_ref(v___y_1906_);
    return v_res_1911_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1912_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1913_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_1914_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1914_, 0, v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1915_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_1916_ = lean_unsigned_to_nat(0);
    v___x_1917_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    lean_ctor_set(v___x_1917_, 1, v___x_1916_);
    lean_ctor_set(v___x_1917_, 2, v___x_1916_);
    lean_ctor_set(v___x_1917_, 3, v___x_1916_);
    lean_ctor_set(v___x_1917_, 4, v___x_1915_);
    lean_ctor_set(v___x_1917_, 5, v___x_1915_);
    lean_ctor_set(v___x_1917_, 6, v___x_1915_);
    lean_ctor_set(v___x_1917_, 7, v___x_1915_);
    lean_ctor_set(v___x_1917_, 8, v___x_1915_);
    lean_ctor_set(v___x_1917_, 9, v___x_1915_);
    return v___x_1917_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    v___x_1918_ = lean_unsigned_to_nat(32);
    v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
    v___x_1920_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1920_, 0, v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    v___x_1921_ = 5usize;
    v___x_1922_ = lean_unsigned_to_nat(0);
    v___x_1923_ = lean_unsigned_to_nat(32);
    v___x_1924_ = lean_mk_empty_array_with_capacity(v___x_1923_);
    v___x_1925_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__3);
    v___x_1926_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1926_, 0, v___x_1925_);
    lean_ctor_set(v___x_1926_, 1, v___x_1924_);
    lean_ctor_set(v___x_1926_, 2, v___x_1922_);
    lean_ctor_set(v___x_1926_, 3, v___x_1922_);
    lean_ctor_set_usize(v___x_1926_, 4, v___x_1921_);
    return v___x_1926_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    v___x_1927_ = lean_box(1);
    v___x_1928_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__4);
    v___x_1929_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_1930_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1930_, 0, v___x_1929_);
    lean_ctor_set(v___x_1930_, 1, v___x_1928_);
    lean_ctor_set(v___x_1930_, 2, v___x_1927_);
    return v___x_1930_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg(
    mut v_msgData_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = lean_st_ref_get(v___y_1932_);
    v_env_1935_ = lean_ctor_get(v___x_1934_, 0);
    lean_inc_ref(v_env_1935_);
    lean_dec(v___x_1934_);
    v___x_1936_ = lean_st_ref_get(v___y_1932_);
    v_scopes_1937_ = lean_ctor_get(v___x_1936_, 2);
    lean_inc(v_scopes_1937_);
    lean_dec(v___x_1936_);
    v___x_1938_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1939_ = l_List_head_x21___redArg(v___x_1938_, v_scopes_1937_);
    lean_dec(v_scopes_1937_);
    v_opts_1940_ = lean_ctor_get(v___x_1939_, 1);
    lean_inc_ref(v_opts_1940_);
    lean_dec(v___x_1939_);
    v___x_1941_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__2);
    v___x_1942_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___closed__5);
    v___x_1943_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1943_, 0, v_env_1935_);
    lean_ctor_set(v___x_1943_, 1, v___x_1941_);
    lean_ctor_set(v___x_1943_, 2, v___x_1942_);
    lean_ctor_set(v___x_1943_, 3, v_opts_1940_);
    v___x_1944_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1944_, 0, v___x_1943_);
    lean_ctor_set(v___x_1944_, 1, v_msgData_1931_);
    v___x_1945_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1945_, 0, v___x_1944_);
    return v___x_1945_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_msgData_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg(v_msgData_1946_, v___y_1947_);
    lean_dec(v___y_1947_);
    return v_res_1949_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__20(
    mut v_opts_1950_: *mut LeanObject,
    mut v_opt_1951_: *mut LeanObject,
) -> u8 {
    let mut v_name_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    v_name_1952_ = lean_ctor_get(v_opt_1951_, 0);
    v_defValue_1953_ = lean_ctor_get(v_opt_1951_, 1);
    v_map_1954_ = lean_ctor_get(v_opts_1950_, 0);
    v___x_1955_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1954_,
            v_name_1952_,
        );
    if lean_obj_tag(v___x_1955_) == 0 {
        let mut v___x_1956_: u8 = 0;
        v___x_1956_ = (lean_unbox(v_defValue_1953_) as u8);
        return v___x_1956_;
    } else {
        let mut v_val_1957_: *mut LeanObject = core::ptr::null_mut();
        v_val_1957_ = lean_ctor_get(v___x_1955_, 0);
        lean_inc(v_val_1957_);
        lean_dec_ref_known(v___x_1955_, 1);
        if lean_obj_tag(v_val_1957_) == 1 {
            let mut v_v_1958_: u8 = 0;
            v_v_1958_ = lean_ctor_get_uint8(v_val_1957_, 0 as u32);
            lean_dec_ref_known(v_val_1957_, 0);
            return v_v_1958_;
        } else {
            let mut v___x_1959_: u8 = 0;
            lean_dec(v_val_1957_);
            v___x_1959_ = (lean_unbox(v_defValue_1953_) as u8);
            return v___x_1959_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__20___boxed(
    mut v_opts_1960_: *mut LeanObject,
    mut v_opt_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1962_: u8 = 0;
    let mut v_r_1963_: *mut LeanObject = core::ptr::null_mut();
    v_res_1962_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__20(v_opts_1960_, v_opt_1961_);
    lean_dec_ref(v_opt_1961_);
    lean_dec_ref(v_opts_1960_);
    v_r_1963_ = lean_box((v_res_1962_) as usize);
    return v_r_1963_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0()
-> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1964_ = lean_box(1);
    v___x_1965_ = l_Lean_MessageData_ofFormat(v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3()
-> *mut LeanObject {
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    v___x_1969_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2;
    v___x_1970_ = l_Lean_MessageData_ofFormat(v___x_1969_);
    return v___x_1970_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21(
    mut v_x_1971_: *mut LeanObject,
    mut v_x_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v_before_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut v_unused_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1972_) == 0 {
                    return v_x_1971_;
                } else {
                    v_head_1973_ = lean_ctor_get(v_x_1972_, 0);
                    v_tail_1974_ = lean_ctor_get(v_x_1972_, 1);
                    v_isSharedCheck_1996_ = (!lean_is_exclusive(v_x_1972_)) as u8;
                    if v_isSharedCheck_1996_ == 0 {
                        v___x_1976_ = v_x_1972_;
                        v_isShared_1977_ = v_isSharedCheck_1996_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1974_);
                        lean_inc(v_head_1973_);
                        lean_dec(v_x_1972_);
                        v___x_1976_ = lean_box(0);
                        v_isShared_1977_ = v_isSharedCheck_1996_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1978_ = lean_ctor_get(v_head_1973_, 0);
                v_isSharedCheck_1994_ = (!lean_is_exclusive(v_head_1973_)) as u8;
                if v_isSharedCheck_1994_ == 0 {
                    v_unused_1995_ = lean_ctor_get(v_head_1973_, 1);
                    lean_dec(v_unused_1995_);
                    v___x_1980_ = v_head_1973_;
                    v_isShared_1981_ = v_isSharedCheck_1994_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_1978_);
                    lean_dec(v_head_1973_);
                    v___x_1980_ = lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_1994_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1982_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0);
                if v_isShared_1981_ == 0 {
                    lean_ctor_set_tag(v___x_1980_, 7);
                    lean_ctor_set(v___x_1980_, 1, v___x_1982_);
                    lean_ctor_set(v___x_1980_, 0, v_x_1971_);
                    v___x_1984_ = v___x_1980_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_x_1971_);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1982_);
                    v___x_1984_ = v_reuseFailAlloc_1993_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1985_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3);
                if v_isShared_1977_ == 0 {
                    lean_ctor_set_tag(v___x_1976_, 7);
                    lean_ctor_set(v___x_1976_, 1, v___x_1985_);
                    lean_ctor_set(v___x_1976_, 0, v___x_1984_);
                    v___x_1987_ = v___x_1976_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1992_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1984_);
                    lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1985_);
                    v___x_1987_ = v_reuseFailAlloc_1992_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1988_ = l_Lean_MessageData_ofSyntax(v_before_1978_);
                v___x_1989_ = l_Lean_indentD(v___x_1988_);
                v___x_1990_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1990_, 0, v___x_1987_);
                lean_ctor_set(v___x_1990_, 1, v___x_1989_);
                v_x_1971_ = v___x_1990_;
                v_x_1972_ = v_tail_1974_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__1;
    v___x_2001_ = l_Lean_MessageData_ofFormat(v___x_2000_);
    return v___x_2001_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg(
    mut v_msgData_2002_: *mut LeanObject,
    mut v_macroStack_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_unused_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2006_ = lean_st_ref_get(v___y_2004_);
                v_scopes_2007_ = lean_ctor_get(v___x_2006_, 2);
                lean_inc(v_scopes_2007_);
                lean_dec(v___x_2006_);
                v___x_2008_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_2009_ = l_List_head_x21___redArg(v___x_2008_, v_scopes_2007_);
                lean_dec(v_scopes_2007_);
                v_opts_2010_ = lean_ctor_get(v___x_2009_, 1);
                lean_inc_ref(v_opts_2010_);
                lean_dec(v___x_2009_);
                v___x_2011_ = l_Lean_Elab_pp_macroStack;
                v___x_2012_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__20(v_opts_2010_, v___x_2011_);
                lean_dec_ref(v_opts_2010_);
                if v___x_2012_ == 0 {
                    lean_dec(v_macroStack_2003_);
                    v___x_2013_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2013_, 0, v_msgData_2002_);
                    return v___x_2013_;
                } else {
                    if lean_obj_tag(v_macroStack_2003_) == 0 {
                        v___x_2014_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2014_, 0, v_msgData_2002_);
                        return v___x_2014_;
                    } else {
                        v_head_2015_ = lean_ctor_get(v_macroStack_2003_, 0);
                        lean_inc(v_head_2015_);
                        v_after_2016_ = lean_ctor_get(v_head_2015_, 1);
                        v_isSharedCheck_2031_ = (!lean_is_exclusive(v_head_2015_)) as u8;
                        if v_isSharedCheck_2031_ == 0 {
                            v_unused_2032_ = lean_ctor_get(v_head_2015_, 0);
                            lean_dec(v_unused_2032_);
                            v___x_2018_ = v_head_2015_;
                            v_isShared_2019_ = v_isSharedCheck_2031_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_2016_);
                            lean_dec(v_head_2015_);
                            v___x_2018_ = lean_box(0);
                            v_isShared_2019_ = v_isSharedCheck_2031_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2020_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0);
                if v_isShared_2019_ == 0 {
                    lean_ctor_set_tag(v___x_2018_, 7);
                    lean_ctor_set(v___x_2018_, 1, v___x_2020_);
                    lean_ctor_set(v___x_2018_, 0, v_msgData_2002_);
                    v___x_2022_ = v___x_2018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_msgData_2002_);
                    lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2020_);
                    v___x_2022_ = v_reuseFailAlloc_2030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2023_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___closed__2);
                v___x_2024_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2024_, 0, v___x_2022_);
                lean_ctor_set(v___x_2024_, 1, v___x_2023_);
                v___x_2025_ = l_Lean_MessageData_ofSyntax(v_after_2016_);
                v___x_2026_ = l_Lean_indentD(v___x_2025_);
                v_msgData_2027_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_2027_, 0, v___x_2024_);
                lean_ctor_set(v_msgData_2027_, 1, v___x_2026_);
                v___x_2028_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18_spec__21(v_msgData_2027_, v_macroStack_2003_);
                v___x_2029_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2029_, 0, v___x_2028_);
                return v___x_2029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg___boxed(
    mut v_msgData_2033_: *mut LeanObject,
    mut v_macroStack_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2037_: *mut LeanObject = core::ptr::null_mut();
    v_res_2037_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg(v_msgData_2033_, v_macroStack_2034_, v___y_2035_);
    lean_dec(v___y_2035_);
    return v_res_2037_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12___redArg(
    mut v_msg_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2052_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2057_: u8 = 0;
    let mut v_a_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2061_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2042_ = l_Lean_Elab_Command_getRef___redArg(v___y_2039_);
                if lean_obj_tag(v___x_2042_) == 0 {
                    v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
                    lean_inc(v_a_2043_);
                    lean_dec_ref_known(v___x_2042_, 1);
                    v_macroStack_2044_ = lean_ctor_get(v___y_2039_, 4);
                    v___x_2045_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg(v_msg_2038_, v___y_2040_);
                    v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
                    lean_inc(v_a_2046_);
                    lean_dec_ref(v___x_2045_);
                    v___x_2047_ = l_Lean_Elab_getBetterRef(v_a_2043_, v_macroStack_2044_);
                    lean_dec(v_a_2043_);
                    lean_inc(v_macroStack_2044_);
                    v___x_2048_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg(v_a_2046_, v_macroStack_2044_, v___y_2040_);
                    v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
                    v_isSharedCheck_2057_ = (!lean_is_exclusive(v___x_2048_)) as u8;
                    if v_isSharedCheck_2057_ == 0 {
                        v___x_2051_ = v___x_2048_;
                        v_isShared_2052_ = v_isSharedCheck_2057_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2049_);
                        lean_dec(v___x_2048_);
                        v___x_2051_ = lean_box(0);
                        v_isShared_2052_ = v_isSharedCheck_2057_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_2038_);
                    v_a_2058_ = lean_ctor_get(v___x_2042_, 0);
                    v_isSharedCheck_2065_ = (!lean_is_exclusive(v___x_2042_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2060_ = v___x_2042_;
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2058_);
                        lean_dec(v___x_2042_);
                        v___x_2060_ = lean_box(0);
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2053_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2053_, 0, v___x_2047_);
                lean_ctor_set(v___x_2053_, 1, v_a_2049_);
                if v_isShared_2052_ == 0 {
                    lean_ctor_set_tag(v___x_2051_, 1);
                    lean_ctor_set(v___x_2051_, 0, v___x_2053_);
                    v___x_2055_ = v___x_2051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
                    v___x_2055_ = v_reuseFailAlloc_2056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2055_;
            }
            3 => {
                if v_isShared_2061_ == 0 {
                    v___x_2063_ = v___x_2060_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12___redArg___boxed(
    mut v_msg_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2070_: *mut LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12___redArg(v_msg_2066_, v___y_2067_, v___y_2068_);
    lean_dec(v___y_2068_);
    lean_dec_ref(v___y_2067_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6___redArg(
    mut v_ref_2071_: *mut LeanObject,
    mut v_msg_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
    mut v___y_2074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2087_: u8 = 0;
    let mut v_ref_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2076_ = l_Lean_Elab_Command_getRef___redArg(v___y_2073_);
                if lean_obj_tag(v___x_2076_) == 0 {
                    v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
                    lean_inc(v_a_2077_);
                    lean_dec_ref_known(v___x_2076_, 1);
                    v_fileName_2078_ = lean_ctor_get(v___y_2073_, 0);
                    v_fileMap_2079_ = lean_ctor_get(v___y_2073_, 1);
                    v_currRecDepth_2080_ = lean_ctor_get(v___y_2073_, 2);
                    v_cmdPos_2081_ = lean_ctor_get(v___y_2073_, 3);
                    v_macroStack_2082_ = lean_ctor_get(v___y_2073_, 4);
                    v_quotContext_x3f_2083_ = lean_ctor_get(v___y_2073_, 5);
                    v_currMacroScope_2084_ = lean_ctor_get(v___y_2073_, 6);
                    v_snap_x3f_2085_ = lean_ctor_get(v___y_2073_, 8);
                    v_cancelTk_x3f_2086_ = lean_ctor_get(v___y_2073_, 9);
                    v_suppressElabErrors_2087_ = lean_ctor_get_uint8(
                        v___y_2073_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_2088_ = l_Lean_replaceRef(v_ref_2071_, v_a_2077_);
                    lean_dec(v_a_2077_);
                    lean_inc(v_cancelTk_x3f_2086_);
                    lean_inc(v_snap_x3f_2085_);
                    lean_inc(v_currMacroScope_2084_);
                    lean_inc(v_quotContext_x3f_2083_);
                    lean_inc(v_macroStack_2082_);
                    lean_inc(v_cmdPos_2081_);
                    lean_inc(v_currRecDepth_2080_);
                    lean_inc_ref(v_fileMap_2079_);
                    lean_inc_ref(v_fileName_2078_);
                    v___x_2089_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_2089_, 0, v_fileName_2078_);
                    lean_ctor_set(v___x_2089_, 1, v_fileMap_2079_);
                    lean_ctor_set(v___x_2089_, 2, v_currRecDepth_2080_);
                    lean_ctor_set(v___x_2089_, 3, v_cmdPos_2081_);
                    lean_ctor_set(v___x_2089_, 4, v_macroStack_2082_);
                    lean_ctor_set(v___x_2089_, 5, v_quotContext_x3f_2083_);
                    lean_ctor_set(v___x_2089_, 6, v_currMacroScope_2084_);
                    lean_ctor_set(v___x_2089_, 7, v_ref_2088_);
                    lean_ctor_set(v___x_2089_, 8, v_snap_x3f_2085_);
                    lean_ctor_set(v___x_2089_, 9, v_cancelTk_x3f_2086_);
                    lean_ctor_set_uint8(
                        v___x_2089_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2087_,
                    );
                    v___x_2090_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12___redArg(v_msg_2072_, v___x_2089_, v___y_2074_);
                    lean_dec_ref_known(v___x_2089_, 10);
                    return v___x_2090_;
                } else {
                    lean_dec_ref(v_msg_2072_);
                    v_a_2091_ = lean_ctor_get(v___x_2076_, 0);
                    v_isSharedCheck_2098_ = (!lean_is_exclusive(v___x_2076_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v___x_2093_ = v___x_2076_;
                        v_isShared_2094_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2091_);
                        lean_dec(v___x_2076_);
                        v___x_2093_ = lean_box(0);
                        v_isShared_2094_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2094_ == 0 {
                    v___x_2096_ = v___x_2093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
                    v___x_2096_ = v_reuseFailAlloc_2097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6___redArg___boxed(
    mut v_ref_2099_: *mut LeanObject,
    mut v_msg_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2104_: *mut LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6___redArg(v_ref_2099_, v_msg_2100_, v___y_2101_, v___y_2102_);
    lean_dec(v___y_2102_);
    lean_dec_ref(v___y_2101_);
    lean_dec(v_ref_2099_);
    return v_res_2104_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__0(
    mut v_env_2105_: *mut LeanObject,
    mut v_declName_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
    mut v___y_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2109_: u8 = 0;
    let mut v_env_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: u8 = 0;
    v___x_2109_ = 0;
    v_env_2110_ = l_Lean_Environment_setExporting(v_env_2105_, v___x_2109_);
    lean_inc(v_declName_2106_);
    v___x_2111_ = l_Lean_mkPrivateName(v_env_2110_, v_declName_2106_);
    v___x_2112_ = 1;
    lean_inc_ref(v_env_2110_);
    v___x_2113_ = l_Lean_Environment_contains(v_env_2110_, v___x_2111_, v___x_2112_);
    if v___x_2113_ == 0 {
        let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2115_: u8 = 0;
        let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
        v___x_2114_ = l_Lean_privateToUserName(v_declName_2106_);
        v___x_2115_ = l_Lean_Environment_contains(v_env_2110_, v___x_2114_, v___x_2112_);
        v___x_2116_ = lean_box((v___x_2115_) as usize);
        v___x_2117_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2117_, 0, v___x_2116_);
        lean_ctor_set(v___x_2117_, 1, v___y_2108_);
        return v___x_2117_;
    } else {
        let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_2110_);
        lean_dec(v_declName_2106_);
        v___x_2118_ = lean_box((v___x_2113_) as usize);
        v___x_2119_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2119_, 0, v___x_2118_);
        lean_ctor_set(v___x_2119_, 1, v___y_2108_);
        return v___x_2119_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__0___boxed(
    mut v_env_2120_: *mut LeanObject,
    mut v_declName_2121_: *mut LeanObject,
    mut v___y_2122_: *mut LeanObject,
    mut v___y_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2124_: *mut LeanObject = core::ptr::null_mut();
    v_res_2124_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__0(
            v_env_2120_,
            v_declName_2121_,
            v___y_2122_,
            v___y_2123_,
        );
    lean_dec_ref(v___y_2122_);
    return v_res_2124_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__0()
-> f64 {
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: f64 = 0.0;
    v___x_2125_ = lean_unsigned_to_nat(0);
    v___x_2126_ = lean_float_of_nat(v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1(
    mut v_cls_2130_: *mut LeanObject,
    mut v_msg_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2141_: u8 = 0;
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v_tid_2157_: u64 = 0;
    let mut v_traces_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: f64 = 0.0;
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v_a_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2135_ = l_Lean_Elab_Command_getRef___redArg(v___y_2132_);
                if lean_obj_tag(v___x_2135_) == 0 {
                    v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
                    lean_inc(v_a_2136_);
                    lean_dec_ref_known(v___x_2135_, 1);
                    v___x_2137_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg(v_msg_2131_, v___y_2133_);
                    v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
                    v_isSharedCheck_2184_ = (!lean_is_exclusive(v___x_2137_)) as u8;
                    if v_isSharedCheck_2184_ == 0 {
                        v___x_2140_ = v___x_2137_;
                        v_isShared_2141_ = v_isSharedCheck_2184_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2138_);
                        lean_dec(v___x_2137_);
                        v___x_2140_ = lean_box(0);
                        v_isShared_2141_ = v_isSharedCheck_2184_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_2131_);
                    lean_dec(v_cls_2130_);
                    v_a_2185_ = lean_ctor_get(v___x_2135_, 0);
                    v_isSharedCheck_2192_ = (!lean_is_exclusive(v___x_2135_)) as u8;
                    if v_isSharedCheck_2192_ == 0 {
                        v___x_2187_ = v___x_2135_;
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2185_);
                        lean_dec(v___x_2135_);
                        v___x_2187_ = lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2142_ = lean_st_ref_take(v___y_2133_);
                v_traceState_2143_ = lean_ctor_get(v___x_2142_, 9);
                v_env_2144_ = lean_ctor_get(v___x_2142_, 0);
                v_messages_2145_ = lean_ctor_get(v___x_2142_, 1);
                v_scopes_2146_ = lean_ctor_get(v___x_2142_, 2);
                v_usedQuotCtxts_2147_ = lean_ctor_get(v___x_2142_, 3);
                v_nextMacroScope_2148_ = lean_ctor_get(v___x_2142_, 4);
                v_maxRecDepth_2149_ = lean_ctor_get(v___x_2142_, 5);
                v_ngen_2150_ = lean_ctor_get(v___x_2142_, 6);
                v_auxDeclNGen_2151_ = lean_ctor_get(v___x_2142_, 7);
                v_infoState_2152_ = lean_ctor_get(v___x_2142_, 8);
                v_snapshotTasks_2153_ = lean_ctor_get(v___x_2142_, 10);
                v_isSharedCheck_2183_ = (!lean_is_exclusive(v___x_2142_)) as u8;
                if v_isSharedCheck_2183_ == 0 {
                    v___x_2155_ = v___x_2142_;
                    v_isShared_2156_ = v_isSharedCheck_2183_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2153_);
                    lean_inc(v_traceState_2143_);
                    lean_inc(v_infoState_2152_);
                    lean_inc(v_auxDeclNGen_2151_);
                    lean_inc(v_ngen_2150_);
                    lean_inc(v_maxRecDepth_2149_);
                    lean_inc(v_nextMacroScope_2148_);
                    lean_inc(v_usedQuotCtxts_2147_);
                    lean_inc(v_scopes_2146_);
                    lean_inc(v_messages_2145_);
                    lean_inc(v_env_2144_);
                    lean_dec(v___x_2142_);
                    v___x_2155_ = lean_box(0);
                    v_isShared_2156_ = v_isSharedCheck_2183_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2157_ = lean_ctor_get_uint64(
                    v_traceState_2143_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2158_ = lean_ctor_get(v_traceState_2143_, 0);
                v_isSharedCheck_2182_ = (!lean_is_exclusive(v_traceState_2143_)) as u8;
                if v_isSharedCheck_2182_ == 0 {
                    v___x_2160_ = v_traceState_2143_;
                    v_isShared_2161_ = v_isSharedCheck_2182_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2158_);
                    lean_dec(v_traceState_2143_);
                    v___x_2160_ = lean_box(0);
                    v_isShared_2161_ = v_isSharedCheck_2182_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2162_ = lean_box(0);
                v___x_2163_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__0);
                v___x_2164_ = 0;
                v___x_2165_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__1;
                v___x_2166_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2166_, 0, v_cls_2130_);
                lean_ctor_set(v___x_2166_, 1, v___x_2162_);
                lean_ctor_set(v___x_2166_, 2, v___x_2165_);
                lean_ctor_set_float(
                    v___x_2166_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2163_,
                );
                lean_ctor_set_float(
                    v___x_2166_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2163_,
                );
                lean_ctor_set_uint8(
                    v___x_2166_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2164_,
                );
                v___x_2167_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__2;
                v___x_2168_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2168_, 0, v___x_2166_);
                lean_ctor_set(v___x_2168_, 1, v_a_2138_);
                lean_ctor_set(v___x_2168_, 2, v___x_2167_);
                v___x_2169_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2169_, 0, v_a_2136_);
                lean_ctor_set(v___x_2169_, 1, v___x_2168_);
                v___x_2170_ = l_Lean_PersistentArray_push___redArg(v_traces_2158_, v___x_2169_);
                if v_isShared_2161_ == 0 {
                    lean_ctor_set(v___x_2160_, 0, v___x_2170_);
                    v___x_2172_ = v___x_2160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2170_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2181_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2157_,
                    );
                    v___x_2172_ = v_reuseFailAlloc_2181_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2156_ == 0 {
                    lean_ctor_set(v___x_2155_, 9, v___x_2172_);
                    v___x_2174_ = v___x_2155_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_env_2144_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_messages_2145_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_scopes_2146_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_usedQuotCtxts_2147_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_nextMacroScope_2148_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 5, v_maxRecDepth_2149_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 6, v_ngen_2150_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 7, v_auxDeclNGen_2151_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 8, v_infoState_2152_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 9, v___x_2172_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 10, v_snapshotTasks_2153_);
                    v___x_2174_ = v_reuseFailAlloc_2180_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2175_ = lean_st_ref_set(v___y_2133_, v___x_2174_);
                v___x_2176_ = lean_box(0);
                if v_isShared_2141_ == 0 {
                    lean_ctor_set(v___x_2140_, 0, v___x_2176_);
                    v___x_2178_ = v___x_2140_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
                    v___x_2178_ = v_reuseFailAlloc_2179_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2178_;
            }
            7 => {
                if v_isShared_2188_ == 0 {
                    v___x_2190_ = v___x_2187_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2190_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___boxed(
    mut v_cls_2193_: *mut LeanObject,
    mut v_msg_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2198_: *mut LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1(v_cls_2193_, v_msg_2194_, v___y_2195_, v___y_2196_);
    lean_dec(v___y_2196_);
    lean_dec_ref(v___y_2195_);
    return v_res_2198_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5(
    mut v_as_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2219_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_2202_) == 0 {
                    v___x_2206_ = lean_box(0);
                    v___x_2207_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2207_, 0, v___x_2206_);
                    return v___x_2207_;
                } else {
                    v_head_2208_ = lean_ctor_get(v_as_2202_, 0);
                    lean_inc(v_head_2208_);
                    v_tail_2209_ = lean_ctor_get(v_as_2202_, 1);
                    lean_inc(v_tail_2209_);
                    lean_dec_ref_known(v_as_2202_, 2);
                    v_fst_2210_ = lean_ctor_get(v_head_2208_, 0);
                    lean_inc(v_fst_2210_);
                    v_snd_2211_ = lean_ctor_get(v_head_2208_, 1);
                    lean_inc(v_snd_2211_);
                    lean_dec(v_head_2208_);
                    v___x_2212_ = l_Lean_inheritedTraceOptions;
                    v___x_2213_ = lean_st_ref_get(v___x_2212_);
                    v___x_2214_ = lean_st_ref_get(v___y_2204_);
                    v_scopes_2215_ = lean_ctor_get(v___x_2214_, 2);
                    lean_inc(v_scopes_2215_);
                    lean_dec(v___x_2214_);
                    v___x_2216_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2217_ = l_List_head_x21___redArg(v___x_2216_, v_scopes_2215_);
                    lean_dec(v_scopes_2215_);
                    v_opts_2218_ = lean_ctor_get(v___x_2217_, 1);
                    lean_inc_ref(v_opts_2218_);
                    lean_dec(v___x_2217_);
                    v_hasTrace_2219_ = lean_ctor_get_uint8(
                        v_opts_2218_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2219_ == 0 {
                        lean_dec_ref(v_opts_2218_);
                        lean_dec(v___x_2213_);
                        lean_dec(v_snd_2211_);
                        lean_dec(v_fst_2210_);
                        v_as_2202_ = v_tail_2209_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2221_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__1;
                        lean_inc(v_fst_2210_);
                        v___x_2222_ = l_Lean_Name_append(v___x_2221_, v_fst_2210_);
                        v___x_2223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_2213_,
                            v_opts_2218_,
                            v___x_2222_,
                        );
                        lean_dec(v___x_2222_);
                        lean_dec_ref(v_opts_2218_);
                        lean_dec(v___x_2213_);
                        if v___x_2223_ == 0 {
                            lean_dec(v_snd_2211_);
                            lean_dec(v_fst_2210_);
                            v_as_2202_ = v_tail_2209_;
                            state = 0;
                            continue;
                        } else {
                            v___x_2225_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_2225_, 0, v_snd_2211_);
                            v___x_2226_ = l_Lean_MessageData_ofFormat(v___x_2225_);
                            v___x_2227_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1(v_fst_2210_, v___x_2226_, v___y_2203_, v___y_2204_);
                            if lean_obj_tag(v___x_2227_) == 0 {
                                lean_dec_ref_known(v___x_2227_, 1);
                                v_as_2202_ = v_tail_2209_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_tail_2209_);
                                return v___x_2227_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___boxed(
    mut v_as_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2233_: *mut LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5(v_as_2229_, v___y_2230_, v___y_2231_);
    lean_dec(v___y_2231_);
    lean_dec_ref(v___y_2230_);
    return v_res_2233_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__4(
    mut v_env_2234_: *mut LeanObject,
    mut v_opts_2235_: *mut LeanObject,
    mut v_currNamespace_2236_: *mut LeanObject,
    mut v_openDecls_2237_: *mut LeanObject,
    mut v_n_2238_: *mut LeanObject,
    mut v___y_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    v___x_2241_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_2234_,
        v_opts_2235_,
        v_currNamespace_2236_,
        v_openDecls_2237_,
        v_n_2238_,
    );
    v___x_2242_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2242_, 0, v___x_2241_);
    lean_ctor_set(v___x_2242_, 1, v___y_2240_);
    return v___x_2242_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__4___boxed(
    mut v_env_2243_: *mut LeanObject,
    mut v_opts_2244_: *mut LeanObject,
    mut v_currNamespace_2245_: *mut LeanObject,
    mut v_openDecls_2246_: *mut LeanObject,
    mut v_n_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__4(
            v_env_2243_,
            v_opts_2244_,
            v_currNamespace_2245_,
            v_openDecls_2246_,
            v_n_2247_,
            v___y_2248_,
            v___y_2249_,
        );
    lean_dec_ref(v___y_2248_);
    lean_dec_ref(v_opts_2244_);
    return v_res_2250_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2___redArg(
    mut v_x_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2251_) == 0 {
        let mut v_a_2253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        v_a_2253_ = lean_ctor_get(v_x_2251_, 0);
        lean_inc(v_a_2253_);
        v___x_2254_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2254_, 0, v_a_2253_);
        lean_ctor_set(v___x_2254_, 1, v___y_2252_);
        return v___x_2254_;
    } else {
        let mut v_a_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        v_a_2255_ = lean_ctor_get(v_x_2251_, 0);
        lean_inc(v_a_2255_);
        v___x_2256_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2256_, 0, v_a_2255_);
        lean_ctor_set(v___x_2256_, 1, v___y_2252_);
        return v___x_2256_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2___redArg___boxed(
    mut v_x_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2259_: *mut LeanObject = core::ptr::null_mut();
    v_res_2259_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2___redArg(v_x_2257_, v___y_2258_);
    lean_dec_ref(v_x_2257_);
    return v_res_2259_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__1(
    mut v_env_2260_: *mut LeanObject,
    mut v_stx_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2274_: u8 = 0;
    let mut v_unused_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v_snd_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2290_: u8 = 0;
    let mut v_a_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut v_a_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2264_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_2260_,
                    v_stx_2261_,
                    v___y_2262_,
                    v___y_2263_,
                );
                if lean_obj_tag(v___x_2264_) == 0 {
                    v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
                    lean_inc(v_a_2265_);
                    if lean_obj_tag(v_a_2265_) == 0 {
                        v_a_2266_ = lean_ctor_get(v___x_2264_, 1);
                        v_isSharedCheck_2274_ = (!lean_is_exclusive(v___x_2264_)) as u8;
                        if v_isSharedCheck_2274_ == 0 {
                            v_unused_2275_ = lean_ctor_get(v___x_2264_, 0);
                            lean_dec(v_unused_2275_);
                            v___x_2268_ = v___x_2264_;
                            v_isShared_2269_ = v_isSharedCheck_2274_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2266_);
                            lean_dec(v___x_2264_);
                            v___x_2268_ = lean_box(0);
                            v_isShared_2269_ = v_isSharedCheck_2274_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_2276_ = lean_ctor_get(v_a_2265_, 0);
                        v_isSharedCheck_2304_ = (!lean_is_exclusive(v_a_2265_)) as u8;
                        if v_isSharedCheck_2304_ == 0 {
                            v___x_2278_ = v_a_2265_;
                            v_isShared_2279_ = v_isSharedCheck_2304_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2276_);
                            lean_dec(v_a_2265_);
                            v___x_2278_ = lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2304_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2305_ = lean_ctor_get(v___x_2264_, 0);
                    v_a_2306_ = lean_ctor_get(v___x_2264_, 1);
                    v_isSharedCheck_2313_ = (!lean_is_exclusive(v___x_2264_)) as u8;
                    if v_isSharedCheck_2313_ == 0 {
                        v___x_2308_ = v___x_2264_;
                        v_isShared_2309_ = v_isSharedCheck_2313_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2306_);
                        lean_inc(v_a_2305_);
                        lean_dec(v___x_2264_);
                        v___x_2308_ = lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2313_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2270_ = lean_box(0);
                if v_isShared_2269_ == 0 {
                    lean_ctor_set(v___x_2268_, 0, v___x_2270_);
                    v___x_2272_ = v___x_2268_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
                    lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_a_2266_);
                    v___x_2272_ = v_reuseFailAlloc_2273_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2272_;
            }
            3 => {
                v_snd_2280_ = lean_ctor_get(v_val_2276_, 1);
                lean_inc(v_snd_2280_);
                lean_dec(v_val_2276_);
                if lean_obj_tag(v_snd_2280_) == 0 {
                    lean_del_object(v___x_2278_);
                    v_a_2281_ = lean_ctor_get(v___x_2264_, 1);
                    lean_inc(v_a_2281_);
                    lean_dec_ref_known(v___x_2264_, 2);
                    v_a_2282_ = lean_ctor_get(v_snd_2280_, 0);
                    v_isSharedCheck_2290_ = (!lean_is_exclusive(v_snd_2280_)) as u8;
                    if v_isSharedCheck_2290_ == 0 {
                        v___x_2284_ = v_snd_2280_;
                        v_isShared_2285_ = v_isSharedCheck_2290_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2282_);
                        lean_dec(v_snd_2280_);
                        v___x_2284_ = lean_box(0);
                        v_isShared_2285_ = v_isSharedCheck_2290_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2291_ = lean_ctor_get(v___x_2264_, 1);
                    lean_inc(v_a_2291_);
                    lean_dec_ref_known(v___x_2264_, 2);
                    v_a_2292_ = lean_ctor_get(v_snd_2280_, 0);
                    v_isSharedCheck_2303_ = (!lean_is_exclusive(v_snd_2280_)) as u8;
                    if v_isSharedCheck_2303_ == 0 {
                        v___x_2294_ = v_snd_2280_;
                        v_isShared_2295_ = v_isSharedCheck_2303_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2292_);
                        lean_dec(v_snd_2280_);
                        v___x_2294_ = lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2303_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2285_ == 0 {
                    v___x_2287_ = v___x_2284_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2282_);
                    v___x_2287_ = v_reuseFailAlloc_2289_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2288_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2___redArg(v___x_2287_, v_a_2281_);
                lean_dec_ref(v___x_2287_);
                return v___x_2288_;
            }
            6 => {
                if v_isShared_2279_ == 0 {
                    lean_ctor_set(v___x_2278_, 0, v_a_2292_);
                    v___x_2297_ = v___x_2278_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2292_);
                    v___x_2297_ = v_reuseFailAlloc_2302_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2295_ == 0 {
                    lean_ctor_set(v___x_2294_, 0, v___x_2297_);
                    v___x_2299_ = v___x_2294_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2297_);
                    v___x_2299_ = v_reuseFailAlloc_2301_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2300_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2___redArg(v___x_2299_, v_a_2291_);
                lean_dec_ref(v___x_2299_);
                return v___x_2300_;
            }
            9 => {
                if v_isShared_2309_ == 0 {
                    v___x_2311_ = v___x_2308_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2305_);
                    lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_a_2306_);
                    v___x_2311_ = v_reuseFailAlloc_2312_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__1___boxed(
    mut v_env_2314_: *mut LeanObject,
    mut v_stx_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2318_: *mut LeanObject = core::ptr::null_mut();
    v_res_2318_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__1(
            v_env_2314_,
            v_stx_2315_,
            v___y_2316_,
            v___y_2317_,
        );
    lean_dec_ref(v___y_2316_);
    return v_res_2318_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    v___x_2324_ = l_Lean_maxRecDepthErrorMessage;
    v___x_2325_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2325_, 0, v___x_2324_);
    return v___x_2325_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    v___x_2326_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__3);
    v___x_2327_ = l_Lean_MessageData_ofFormat(v___x_2326_);
    return v___x_2327_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    v___x_2328_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__4);
    v___x_2329_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__2;
    v___x_2330_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_2330_, 0, v___x_2329_);
    lean_ctor_set(v___x_2330_, 1, v___x_2328_);
    return v___x_2330_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg(
    mut v_ref_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v___x_2333_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___closed__5);
    v___x_2334_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2334_, 0, v_ref_2331_);
    lean_ctor_set(v___x_2334_, 1, v___x_2333_);
    v___x_2335_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2335_, 0, v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg___boxed(
    mut v_ref_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2338_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg(v_ref_2336_);
    return v_res_2338_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__3(
    mut v_env_2339_: *mut LeanObject,
    mut v_currNamespace_2340_: *mut LeanObject,
    mut v_openDecls_2341_: *mut LeanObject,
    mut v_n_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Lean_ResolveName_resolveNamespace(
        v_env_2339_,
        v_currNamespace_2340_,
        v_openDecls_2341_,
        v_n_2342_,
    );
    v___x_2346_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2346_, 0, v___x_2345_);
    lean_ctor_set(v___x_2346_, 1, v___y_2344_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__3___boxed(
    mut v_env_2347_: *mut LeanObject,
    mut v_currNamespace_2348_: *mut LeanObject,
    mut v_openDecls_2349_: *mut LeanObject,
    mut v_n_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_res_2353_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__3(
            v_env_2347_,
            v_currNamespace_2348_,
            v_openDecls_2349_,
            v_n_2350_,
            v___y_2351_,
            v___y_2352_,
        );
    lean_dec_ref(v___y_2351_);
    return v_res_2353_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13___redArg(
    mut v_a_2354_: *mut LeanObject,
    mut v_x_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2355_) == 0 {
                    v___x_2356_ = lean_box(0);
                    return v___x_2356_;
                } else {
                    v_key_2357_ = lean_ctor_get(v_x_2355_, 0);
                    v_value_2358_ = lean_ctor_get(v_x_2355_, 1);
                    v_tail_2359_ = lean_ctor_get(v_x_2355_, 2);
                    v___x_2360_ = lean_name_eq(v_key_2357_, v_a_2354_);
                    if v___x_2360_ == 0 {
                        v_x_2355_ = v_tail_2359_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2358_);
                        v___x_2362_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2362_, 0, v_value_2358_);
                        return v___x_2362_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13___redArg___boxed(
    mut v_a_2363_: *mut LeanObject,
    mut v_x_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2365_: *mut LeanObject = core::ptr::null_mut();
    v_res_2365_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13___redArg(v_a_2363_, v_x_2364_);
    lean_dec(v_x_2364_);
    lean_dec(v_a_2363_);
    return v_res_2365_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg___closed__0()
-> u64 {
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: u64 = 0;
    v___x_2366_ = lean_unsigned_to_nat(1723);
    v___x_2367_ = lean_uint64_of_nat(v___x_2366_);
    return v___x_2367_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg(
    mut v_m_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2373_: u64 = 0;
    let mut v___x_2374_: u64 = 0;
    let mut v___x_2375_: u64 = 0;
    let mut v_fold_2376_: u64 = 0;
    let mut v___x_2377_: u64 = 0;
    let mut v___x_2378_: u64 = 0;
    let mut v___x_2379_: u64 = 0;
    let mut v___x_2380_: usize = 0;
    let mut v___x_2381_: usize = 0;
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: usize = 0;
    let mut v___x_2384_: usize = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u64 = 0;
    let mut v_hash_2388_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2370_ = lean_ctor_get(v_m_2368_, 1);
                v___x_2371_ = lean_array_get_size(v_buckets_2370_);
                if lean_obj_tag(v_a_2369_) == 0 {
                    v___x_2387_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg___closed__0);
                    v___y_2373_ = v___x_2387_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2388_ = lean_ctor_get_uint64(
                        v_a_2369_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2373_ = v_hash_2388_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2374_ = 32u64;
                v___x_2375_ = lean_uint64_shift_right(v___y_2373_, v___x_2374_);
                v_fold_2376_ = lean_uint64_xor(v___y_2373_, v___x_2375_);
                v___x_2377_ = 16u64;
                v___x_2378_ = lean_uint64_shift_right(v_fold_2376_, v___x_2377_);
                v___x_2379_ = lean_uint64_xor(v_fold_2376_, v___x_2378_);
                v___x_2380_ = lean_uint64_to_usize(v___x_2379_);
                v___x_2381_ = lean_usize_of_nat(v___x_2371_);
                v___x_2382_ = 1usize;
                v___x_2383_ = lean_usize_sub(v___x_2381_, v___x_2382_);
                v___x_2384_ = lean_usize_land(v___x_2380_, v___x_2383_);
                v___x_2385_ = lean_array_uget_borrowed(v_buckets_2370_, v___x_2384_);
                v___x_2386_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13___redArg(v_a_2369_, v___x_2385_);
                return v___x_2386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_m_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2391_: *mut LeanObject = core::ptr::null_mut();
    v_res_2391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg(v_m_2389_, v_a_2390_);
    lean_dec(v_a_2390_);
    lean_dec_ref(v_m_2389_);
    return v_res_2391_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(
    mut v_keys_2392_: *mut LeanObject,
    mut v_i_2393_: *mut LeanObject,
    mut v_k_2394_: *mut LeanObject,
) -> u8 {
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: u8 = 0;
    let mut v_k_x27_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2395_ = lean_array_get_size(v_keys_2392_);
                v___x_2396_ = lean_nat_dec_lt(v_i_2393_, v___x_2395_);
                if v___x_2396_ == 0 {
                    lean_dec(v_i_2393_);
                    return v___x_2396_;
                } else {
                    v_k_x27_2397_ = lean_array_fget_borrowed(v_keys_2392_, v_i_2393_);
                    v___x_2398_ = l_Lean_instBEqExtraModUse_beq(v_k_2394_, v_k_x27_2397_);
                    if v___x_2398_ == 0 {
                        v___x_2399_ = lean_unsigned_to_nat(1);
                        v___x_2400_ = lean_nat_add(v_i_2393_, v___x_2399_);
                        lean_dec(v_i_2393_);
                        v_i_2393_ = v___x_2400_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_2393_);
                        return v___x_2398_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg___boxed(
    mut v_keys_2402_: *mut LeanObject,
    mut v_i_2403_: *mut LeanObject,
    mut v_k_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2405_: u8 = 0;
    let mut v_r_2406_: *mut LeanObject = core::ptr::null_mut();
    v_res_2405_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(v_keys_2402_, v_i_2403_, v_k_2404_);
    lean_dec_ref(v_k_2404_);
    lean_dec_ref(v_keys_2402_);
    v_r_2406_ = lean_box((v_res_2405_) as usize);
    return v_r_2406_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0()
-> usize {
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: usize = 0;
    let mut v___x_2409_: usize = 0;
    v___x_2407_ = 5usize;
    v___x_2408_ = 1usize;
    v___x_2409_ = lean_usize_shift_left(v___x_2408_, v___x_2407_);
    return v___x_2409_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1()
-> usize {
    let mut v___x_2410_: usize = 0;
    let mut v___x_2411_: usize = 0;
    let mut v___x_2412_: usize = 0;
    v___x_2410_ = 1usize;
    v___x_2411_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0);
    v___x_2412_ = lean_usize_sub(v___x_2411_, v___x_2410_);
    return v___x_2412_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(
    mut v_x_2413_: *mut LeanObject,
    mut v_x_2414_: usize,
    mut v_x_2415_: *mut LeanObject,
) -> u8 {
    let mut v_es_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: usize = 0;
    let mut v___x_2419_: usize = 0;
    let mut v___x_2420_: usize = 0;
    let mut v_j_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v_node_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: usize = 0;
    let mut v___x_2428_: u8 = 0;
    let mut v_ks_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2413_) == 0 {
                    v_es_2416_ = lean_ctor_get(v_x_2413_, 0);
                    v___x_2417_ = lean_box(2);
                    v___x_2418_ = 5usize;
                    v___x_2419_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1);
                    v___x_2420_ = lean_usize_land(v_x_2414_, v___x_2419_);
                    v_j_2421_ = lean_usize_to_nat(v___x_2420_);
                    v___x_2422_ = lean_array_get_borrowed(v___x_2417_, v_es_2416_, v_j_2421_);
                    lean_dec(v_j_2421_);
                    match lean_obj_tag(v___x_2422_) {
                        0 => {
                            v_key_2423_ = lean_ctor_get(v___x_2422_, 0);
                            v___x_2424_ = l_Lean_instBEqExtraModUse_beq(v_x_2415_, v_key_2423_);
                            return v___x_2424_;
                        }
                        1 => {
                            v_node_2425_ = lean_ctor_get(v___x_2422_, 0);
                            v___x_2426_ = lean_usize_shift_right(v_x_2414_, v___x_2418_);
                            v_x_2413_ = v_node_2425_;
                            v_x_2414_ = v___x_2426_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2428_ = 0;
                            return v___x_2428_;
                        }
                    }
                } else {
                    v_ks_2429_ = lean_ctor_get(v_x_2413_, 0);
                    v___x_2430_ = lean_unsigned_to_nat(0);
                    v___x_2431_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(v_ks_2429_, v___x_2430_, v_x_2415_);
                    return v___x_2431_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___boxed(
    mut v_x_2432_: *mut LeanObject,
    mut v_x_2433_: *mut LeanObject,
    mut v_x_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_21723__boxed_2435_: usize = 0;
    let mut v_res_2436_: u8 = 0;
    let mut v_r_2437_: *mut LeanObject = core::ptr::null_mut();
    v_x_21723__boxed_2435_ = lean_unbox_usize(v_x_2433_);
    lean_dec(v_x_2433_);
    v_res_2436_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(v_x_2432_, v_x_21723__boxed_2435_, v_x_2434_);
    lean_dec_ref(v_x_2434_);
    lean_dec_ref(v_x_2432_);
    v_r_2437_ = lean_box((v_res_2436_) as usize);
    return v_r_2437_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10___redArg(
    mut v_x_2438_: *mut LeanObject,
    mut v_x_2439_: *mut LeanObject,
) -> u8 {
    let mut v___x_2440_: u64 = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: u8 = 0;
    v___x_2440_ = l_Lean_instHashableExtraModUse_hash(v_x_2439_);
    v___x_2441_ = lean_uint64_to_usize(v___x_2440_);
    v___x_2442_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(v_x_2438_, v___x_2441_, v_x_2439_);
    return v___x_2442_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10___redArg___boxed(
    mut v_x_2443_: *mut LeanObject,
    mut v_x_2444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2445_: u8 = 0;
    let mut v_r_2446_: *mut LeanObject = core::ptr::null_mut();
    v_res_2445_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10___redArg(v_x_2443_, v_x_2444_);
    lean_dec_ref(v_x_2444_);
    lean_dec_ref(v_x_2443_);
    v_r_2446_ = lean_box((v_res_2445_) as usize);
    return v_r_2446_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__2()
-> *mut LeanObject {
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    v___x_2449_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__1;
    v___x_2450_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__0;
    v___x_2451_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2450_, v___x_2449_);
    return v___x_2451_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__6()
-> *mut LeanObject {
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2456_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__5;
    v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
    return v___x_2457_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__8()
-> *mut LeanObject {
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2459_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__7;
    v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
    return v___x_2460_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__9()
-> *mut LeanObject {
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    v___x_2461_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1___closed__1;
    v___x_2462_ = l_Lean_stringToMessageData(v___x_2461_);
    return v___x_2462_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__10()
-> *mut LeanObject {
    let mut v_cls_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    v_cls_2463_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__4;
    v___x_2464_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5___closed__1;
    v___x_2465_ = l_Lean_Name_append(v___x_2464_, v_cls_2463_);
    return v___x_2465_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__12()
-> *mut LeanObject {
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    v___x_2467_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__11;
    v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
    return v___x_2468_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__14()
-> *mut LeanObject {
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v___x_2470_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__13;
    v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
    return v___x_2471_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6(
    mut v_mod_2476_: *mut LeanObject,
    mut v_isMeta_2477_: u8,
    mut v_hint_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2484_: u8 = 0;
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2509_: u8 = 0;
    let mut v_asyncMode_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: u8 = 0;
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2528_: u8 = 0;
    let mut v_cls_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2482_ = lean_st_ref_get(v___y_2480_);
                v_env_2483_ = lean_ctor_get(v___x_2482_, 0);
                lean_inc_ref(v_env_2483_);
                lean_dec(v___x_2482_);
                v_isExporting_2484_ = lean_ctor_get_uint8(
                    v_env_2483_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_2483_);
                v___x_2485_ = lean_st_ref_get(v___y_2480_);
                v_env_2486_ = lean_ctor_get(v___x_2485_, 0);
                lean_inc_ref(v_env_2486_);
                lean_dec(v___x_2485_);
                v___x_2487_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__2);
                lean_inc(v_mod_2476_);
                v_entry_2488_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_2488_, 0, v_mod_2476_);
                lean_ctor_set_uint8(
                    v_entry_2488_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_2484_,
                );
                lean_ctor_set_uint8(
                    v_entry_2488_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_2477_,
                );
                v___x_2489_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_2490_ = lean_box(1);
                v___x_2491_ = lean_box(0);
                v___x_2519_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_2487_,
                    v___x_2489_,
                    v_env_2486_,
                    v___x_2490_,
                    v___x_2491_,
                );
                v___x_2520_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10___redArg(v___x_2519_, v_entry_2488_);
                lean_dec(v___x_2519_);
                if v___x_2520_ == 0 {
                    v___x_2521_ = l_Lean_inheritedTraceOptions;
                    v___x_2522_ = lean_st_ref_get(v___x_2521_);
                    v___x_2523_ = lean_st_ref_get(v___y_2480_);
                    v_scopes_2524_ = lean_ctor_get(v___x_2523_, 2);
                    lean_inc(v_scopes_2524_);
                    lean_dec(v___x_2523_);
                    v___x_2525_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2526_ = l_List_head_x21___redArg(v___x_2525_, v_scopes_2524_);
                    lean_dec(v_scopes_2524_);
                    v_opts_2527_ = lean_ctor_get(v___x_2526_, 1);
                    lean_inc_ref(v_opts_2527_);
                    lean_dec(v___x_2526_);
                    v_hasTrace_2528_ = lean_ctor_get_uint8(
                        v_opts_2527_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2528_ == 0 {
                        lean_dec_ref(v_opts_2527_);
                        lean_dec(v___x_2522_);
                        lean_dec(v_hint_2478_);
                        lean_dec(v_mod_2476_);
                        v___y_2493_ = v___y_2480_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_2529_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__4;
                        v___x_2549_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__10);
                        v___x_2550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_2522_,
                            v_opts_2527_,
                            v___x_2549_,
                        );
                        lean_dec_ref(v_opts_2527_);
                        lean_dec(v___x_2522_);
                        if v___x_2550_ == 0 {
                            lean_dec(v_hint_2478_);
                            lean_dec(v_mod_2476_);
                            v___y_2493_ = v___y_2480_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2551_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__12);
                            if v_isExporting_2484_ == 0 {
                                v___x_2560_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__17;
                                v___y_2553_ = v___x_2560_;
                                state = 6;
                                continue;
                            } else {
                                v___x_2561_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__18;
                                v___y_2553_ = v___x_2561_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v_entry_2488_, 1);
                    lean_dec(v_hint_2478_);
                    lean_dec(v_mod_2476_);
                    v___x_2562_ = lean_box(0);
                    v___x_2563_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2563_, 0, v___x_2562_);
                    return v___x_2563_;
                }
            }
            1 => {
                v___x_2494_ = lean_st_ref_take(v___y_2493_);
                v_toEnvExtension_2495_ = lean_ctor_get(v___x_2489_, 0);
                v_env_2496_ = lean_ctor_get(v___x_2494_, 0);
                v_messages_2497_ = lean_ctor_get(v___x_2494_, 1);
                v_scopes_2498_ = lean_ctor_get(v___x_2494_, 2);
                v_usedQuotCtxts_2499_ = lean_ctor_get(v___x_2494_, 3);
                v_nextMacroScope_2500_ = lean_ctor_get(v___x_2494_, 4);
                v_maxRecDepth_2501_ = lean_ctor_get(v___x_2494_, 5);
                v_ngen_2502_ = lean_ctor_get(v___x_2494_, 6);
                v_auxDeclNGen_2503_ = lean_ctor_get(v___x_2494_, 7);
                v_infoState_2504_ = lean_ctor_get(v___x_2494_, 8);
                v_traceState_2505_ = lean_ctor_get(v___x_2494_, 9);
                v_snapshotTasks_2506_ = lean_ctor_get(v___x_2494_, 10);
                v_isSharedCheck_2518_ = (!lean_is_exclusive(v___x_2494_)) as u8;
                if v_isSharedCheck_2518_ == 0 {
                    v___x_2508_ = v___x_2494_;
                    v_isShared_2509_ = v_isSharedCheck_2518_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2506_);
                    lean_inc(v_traceState_2505_);
                    lean_inc(v_infoState_2504_);
                    lean_inc(v_auxDeclNGen_2503_);
                    lean_inc(v_ngen_2502_);
                    lean_inc(v_maxRecDepth_2501_);
                    lean_inc(v_nextMacroScope_2500_);
                    lean_inc(v_usedQuotCtxts_2499_);
                    lean_inc(v_scopes_2498_);
                    lean_inc(v_messages_2497_);
                    lean_inc(v_env_2496_);
                    lean_dec(v___x_2494_);
                    v___x_2508_ = lean_box(0);
                    v_isShared_2509_ = v_isSharedCheck_2518_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_2510_ = lean_ctor_get(v_toEnvExtension_2495_, 2);
                v___x_2511_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2489_,
                    v_env_2496_,
                    v_entry_2488_,
                    v_asyncMode_2510_,
                    v___x_2491_,
                );
                if v_isShared_2509_ == 0 {
                    lean_ctor_set(v___x_2508_, 0, v___x_2511_);
                    v___x_2513_ = v___x_2508_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2511_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_messages_2497_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_scopes_2498_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_usedQuotCtxts_2499_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_nextMacroScope_2500_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 5, v_maxRecDepth_2501_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 6, v_ngen_2502_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 7, v_auxDeclNGen_2503_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 8, v_infoState_2504_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 9, v_traceState_2505_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 10, v_snapshotTasks_2506_);
                    v___x_2513_ = v_reuseFailAlloc_2517_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2514_ = lean_st_ref_set(v___y_2493_, v___x_2513_);
                v___x_2515_ = lean_box(0);
                v___x_2516_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2516_, 0, v___x_2515_);
                return v___x_2516_;
            }
            4 => {
                v___x_2533_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2533_, 0, v___y_2531_);
                lean_ctor_set(v___x_2533_, 1, v___y_2532_);
                v___x_2534_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1(v_cls_2529_, v___x_2533_, v___y_2479_, v___y_2480_);
                if lean_obj_tag(v___x_2534_) == 0 {
                    lean_dec_ref_known(v___x_2534_, 1);
                    v___y_2493_ = v___y_2480_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_2488_, 1);
                    return v___x_2534_;
                }
            }
            5 => {
                lean_inc_ref(v___y_2537_);
                v___x_2538_ = l_Lean_stringToMessageData(v___y_2537_);
                v___x_2539_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2539_, 0, v___y_2536_);
                lean_ctor_set(v___x_2539_, 1, v___x_2538_);
                v___x_2540_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__6);
                v___x_2541_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2541_, 0, v___x_2539_);
                lean_ctor_set(v___x_2541_, 1, v___x_2540_);
                v___x_2542_ = l_Lean_MessageData_ofName(v_mod_2476_);
                v___x_2543_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2543_, 0, v___x_2541_);
                lean_ctor_set(v___x_2543_, 1, v___x_2542_);
                v___x_2544_ = l_Lean_Name_isAnonymous(v_hint_2478_);
                if v___x_2544_ == 0 {
                    v___x_2545_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__8);
                    v___x_2546_ = l_Lean_MessageData_ofName(v_hint_2478_);
                    v___x_2547_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2547_, 0, v___x_2545_);
                    lean_ctor_set(v___x_2547_, 1, v___x_2546_);
                    v___y_2531_ = v___x_2543_;
                    v___y_2532_ = v___x_2547_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_2478_);
                    v___x_2548_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__9);
                    v___y_2531_ = v___x_2543_;
                    v___y_2532_ = v___x_2548_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_2553_);
                v___x_2554_ = l_Lean_stringToMessageData(v___y_2553_);
                v___x_2555_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2555_, 0, v___x_2551_);
                lean_ctor_set(v___x_2555_, 1, v___x_2554_);
                v___x_2556_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__14);
                v___x_2557_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2557_, 0, v___x_2555_);
                lean_ctor_set(v___x_2557_, 1, v___x_2556_);
                if v_isMeta_2477_ == 0 {
                    v___x_2558_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__15;
                    v___y_2536_ = v___x_2557_;
                    v___y_2537_ = v___x_2558_;
                    state = 5;
                    continue;
                } else {
                    v___x_2559_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___closed__16;
                    v___y_2536_ = v___x_2557_;
                    v___y_2537_ = v___x_2559_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6___boxed(
    mut v_mod_2564_: *mut LeanObject,
    mut v_isMeta_2565_: *mut LeanObject,
    mut v_hint_2566_: *mut LeanObject,
    mut v___y_2567_: *mut LeanObject,
    mut v___y_2568_: *mut LeanObject,
    mut v___y_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2570_: u8 = 0;
    let mut v_res_2571_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2570_ = (lean_unbox(v_isMeta_2565_) as u8);
    v_res_2571_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6(v_mod_2564_, v_isMeta_boxed_2570_, v_hint_2566_, v___y_2567_, v___y_2568_);
    lean_dec(v___y_2568_);
    lean_dec_ref(v___y_2567_);
    return v_res_2571_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__7(
    mut v___x_2572_: *mut LeanObject,
    mut v_declName_2573_: *mut LeanObject,
    mut v_as_2574_: *mut LeanObject,
    mut v_sz_2575_: usize,
    mut v_i_2576_: usize,
    mut v_b_2577_: *mut LeanObject,
    mut v___y_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: usize = 0;
    let mut v___x_2594_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2581_ = lean_usize_dec_lt(v_i_2576_, v_sz_2575_);
                if v___x_2581_ == 0 {
                    lean_dec(v_declName_2573_);
                    v___x_2582_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2582_, 0, v_b_2577_);
                    return v___x_2582_;
                } else {
                    v___x_2583_ = l_Lean_Environment_header(v___x_2572_);
                    v_modules_2584_ = lean_ctor_get(v___x_2583_, 3);
                    lean_inc_ref(v_modules_2584_);
                    lean_dec_ref(v___x_2583_);
                    v___x_2585_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_2586_ = lean_array_uget_borrowed(v_as_2574_, v_i_2576_);
                    v___x_2587_ = lean_array_get(v___x_2585_, v_modules_2584_, v_a_2586_);
                    lean_dec_ref(v_modules_2584_);
                    v_toImport_2588_ = lean_ctor_get(v___x_2587_, 0);
                    lean_inc_ref(v_toImport_2588_);
                    lean_dec(v___x_2587_);
                    v_module_2589_ = lean_ctor_get(v_toImport_2588_, 0);
                    lean_inc(v_module_2589_);
                    lean_dec_ref(v_toImport_2588_);
                    v___x_2590_ = 0;
                    lean_inc(v_declName_2573_);
                    v___x_2591_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6(v_module_2589_, v___x_2590_, v_declName_2573_, v___y_2578_, v___y_2579_);
                    if lean_obj_tag(v___x_2591_) == 0 {
                        lean_dec_ref_known(v___x_2591_, 1);
                        v___x_2592_ = lean_box(0);
                        v___x_2593_ = 1usize;
                        v___x_2594_ = lean_usize_add(v_i_2576_, v___x_2593_);
                        v_i_2576_ = v___x_2594_;
                        v_b_2577_ = v___x_2592_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_2573_);
                        return v___x_2591_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__7___boxed(
    mut v___x_2596_: *mut LeanObject,
    mut v_declName_2597_: *mut LeanObject,
    mut v_as_2598_: *mut LeanObject,
    mut v_sz_2599_: *mut LeanObject,
    mut v_i_2600_: *mut LeanObject,
    mut v_b_2601_: *mut LeanObject,
    mut v___y_2602_: *mut LeanObject,
    mut v___y_2603_: *mut LeanObject,
    mut v___y_2604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2605_: usize = 0;
    let mut v_i_boxed_2606_: usize = 0;
    let mut v_res_2607_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2605_ = lean_unbox_usize(v_sz_2599_);
    lean_dec(v_sz_2599_);
    v_i_boxed_2606_ = lean_unbox_usize(v_i_2600_);
    lean_dec(v_i_2600_);
    v_res_2607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__7(v___x_2596_, v_declName_2597_, v_as_2598_, v_sz_boxed_2605_, v_i_boxed_2606_, v_b_2601_, v___y_2602_, v___y_2603_);
    lean_dec(v___y_2603_);
    lean_dec_ref(v___y_2602_);
    lean_dec_ref(v_as_2598_);
    lean_dec_ref(v___x_2596_);
    return v_res_2607_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    v___x_2610_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__1;
    v___x_2611_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__0;
    v___x_2612_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2611_, v___x_2610_);
    return v___x_2612_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3(
    mut v_declName_2615_: *mut LeanObject,
    mut v_isMeta_2616_: u8,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2628_: usize = 0;
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2633_: u8 = 0;
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut v_unused_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: u8 = 0;
    let mut v_toImport_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: u8 = 0;
    let mut v___x_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2620_ = lean_st_ref_get(v___y_2618_);
                v_env_2624_ = lean_ctor_get(v___x_2620_, 0);
                lean_inc_ref(v_env_2624_);
                lean_dec(v___x_2620_);
                v___x_2639_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2624_, v_declName_2615_);
                if lean_obj_tag(v___x_2639_) == 0 {
                    lean_dec_ref(v_env_2624_);
                    lean_dec(v_declName_2615_);
                    state = 1;
                    continue;
                } else {
                    v_val_2640_ = lean_ctor_get(v___x_2639_, 0);
                    lean_inc(v_val_2640_);
                    lean_dec_ref_known(v___x_2639_, 1);
                    v___x_2641_ = l_Lean_Environment_header(v_env_2624_);
                    v_modules_2642_ = lean_ctor_get(v___x_2641_, 3);
                    lean_inc_ref(v_modules_2642_);
                    lean_dec_ref(v___x_2641_);
                    v___x_2643_ = lean_array_get_size(v_modules_2642_);
                    v___x_2644_ = lean_nat_dec_lt(v_val_2640_, v___x_2643_);
                    if v___x_2644_ == 0 {
                        lean_dec_ref(v_modules_2642_);
                        lean_dec(v_val_2640_);
                        lean_dec_ref(v_env_2624_);
                        lean_dec(v_declName_2615_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2645_ = lean_st_ref_get(v___y_2618_);
                        v_env_2646_ = lean_ctor_get(v___x_2645_, 0);
                        lean_inc_ref(v_env_2646_);
                        lean_dec(v___x_2645_);
                        v___x_2647_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__2);
                        v___x_2648_ = lean_array_fget(v_modules_2642_, v_val_2640_);
                        lean_dec(v_val_2640_);
                        lean_dec_ref(v_modules_2642_);
                        if v_isMeta_2616_ == 0 {
                            lean_dec_ref(v_env_2646_);
                            v___y_2650_ = v_isMeta_2616_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_2615_);
                            v___x_2661_ = l_Lean_isMarkedMeta(v_env_2646_, v_declName_2615_);
                            if v___x_2661_ == 0 {
                                v___y_2650_ = v_isMeta_2616_;
                                state = 5;
                                continue;
                            } else {
                                v___x_2662_ = 0;
                                v___y_2650_ = v___x_2662_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2622_ = lean_box(0);
                v___x_2623_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2623_, 0, v___x_2622_);
                return v___x_2623_;
            }
            2 => {
                v___x_2627_ = lean_box(0);
                v_sz_2628_ = lean_array_size(v___y_2626_);
                v___x_2629_ = 0usize;
                v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__7(v_env_2624_, v_declName_2615_, v___y_2626_, v_sz_2628_, v___x_2629_, v___x_2627_, v___y_2617_, v___y_2618_);
                lean_dec_ref(v___y_2626_);
                lean_dec_ref(v_env_2624_);
                if lean_obj_tag(v___x_2630_) == 0 {
                    v_isSharedCheck_2637_ = (!lean_is_exclusive(v___x_2630_)) as u8;
                    if v_isSharedCheck_2637_ == 0 {
                        v_unused_2638_ = lean_ctor_get(v___x_2630_, 0);
                        lean_dec(v_unused_2638_);
                        v___x_2632_ = v___x_2630_;
                        v_isShared_2633_ = v_isSharedCheck_2637_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2630_);
                        v___x_2632_ = lean_box(0);
                        v_isShared_2633_ = v_isSharedCheck_2637_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_2630_;
                }
            }
            3 => {
                if v_isShared_2633_ == 0 {
                    lean_ctor_set(v___x_2632_, 0, v___x_2627_);
                    v___x_2635_ = v___x_2632_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2627_);
                    v___x_2635_ = v_reuseFailAlloc_2636_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2635_;
            }
            5 => {
                v_toImport_2651_ = lean_ctor_get(v___x_2648_, 0);
                lean_inc_ref(v_toImport_2651_);
                lean_dec(v___x_2648_);
                v_module_2652_ = lean_ctor_get(v_toImport_2651_, 0);
                lean_inc(v_module_2652_);
                lean_dec_ref(v_toImport_2651_);
                lean_inc(v_declName_2615_);
                v___x_2653_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6(v_module_2652_, v___y_2650_, v_declName_2615_, v___y_2617_, v___y_2618_);
                if lean_obj_tag(v___x_2653_) == 0 {
                    lean_dec_ref_known(v___x_2653_, 1);
                    v___x_2654_ = l_Lean_indirectModUseExt;
                    v___x_2655_ = lean_box(1);
                    v___x_2656_ = lean_box(0);
                    lean_inc_ref(v_env_2624_);
                    v___x_2657_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_2647_,
                        v___x_2654_,
                        v_env_2624_,
                        v___x_2655_,
                        v___x_2656_,
                    );
                    v___x_2658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg(v___x_2657_, v_declName_2615_);
                    lean_dec(v___x_2657_);
                    if lean_obj_tag(v___x_2658_) == 0 {
                        v___x_2659_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___closed__3;
                        v___y_2626_ = v___x_2659_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2660_ = lean_ctor_get(v___x_2658_, 0);
                        lean_inc(v_val_2660_);
                        lean_dec_ref_known(v___x_2658_, 1);
                        v___y_2626_ = v_val_2660_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_2624_);
                    lean_dec(v_declName_2615_);
                    return v___x_2653_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3___boxed(
    mut v_declName_2663_: *mut LeanObject,
    mut v_isMeta_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2668_: u8 = 0;
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2668_ = (lean_unbox(v_isMeta_2664_) as u8);
    v_res_2669_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3(v_declName_2663_, v_isMeta_boxed_2668_, v___y_2665_, v___y_2666_);
    lean_dec(v___y_2666_);
    lean_dec_ref(v___y_2665_);
    return v_res_2669_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4___redArg(
    mut v_as_x27_2670_: *mut LeanObject,
    mut v_b_2671_: *mut LeanObject,
    mut v___y_2672_: *mut LeanObject,
    mut v___y_2673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2670_) == 0 {
                    v___x_2675_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2675_, 0, v_b_2671_);
                    return v___x_2675_;
                } else {
                    v_head_2676_ = lean_ctor_get(v_as_x27_2670_, 0);
                    v_tail_2677_ = lean_ctor_get(v_as_x27_2670_, 1);
                    v___x_2678_ = 1;
                    lean_inc(v_head_2676_);
                    v___x_2679_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3(v_head_2676_, v___x_2678_, v___y_2672_, v___y_2673_);
                    if lean_obj_tag(v___x_2679_) == 0 {
                        lean_dec_ref_known(v___x_2679_, 1);
                        v___x_2680_ = lean_box(0);
                        v_as_x27_2670_ = v_tail_2677_;
                        v_b_2671_ = v___x_2680_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2679_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4___redArg___boxed(
    mut v_as_x27_2682_: *mut LeanObject,
    mut v_b_2683_: *mut LeanObject,
    mut v___y_2684_: *mut LeanObject,
    mut v___y_2685_: *mut LeanObject,
    mut v___y_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2687_: *mut LeanObject = core::ptr::null_mut();
    v_res_2687_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4___redArg(v_as_x27_2682_, v_b_2683_, v___y_2684_, v___y_2685_);
    lean_dec(v___y_2685_);
    lean_dec_ref(v___y_2684_);
    lean_dec(v_as_x27_2682_);
    return v_res_2687_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__2(
    mut v_currNamespace_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    v___x_2691_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2691_, 0, v_currNamespace_2688_);
    lean_ctor_set(v___x_2691_, 1, v___y_2690_);
    return v___x_2691_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__2___boxed(
    mut v_currNamespace_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2695_: *mut LeanObject = core::ptr::null_mut();
    v_res_2695_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__2(
            v_currNamespace_2692_,
            v___y_2693_,
            v___y_2694_,
        );
    lean_dec_ref(v___y_2693_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg(
    mut v_x_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroScope_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut v_unused_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2773_: u8 = 0;
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut v_reuseFailAlloc_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_unused_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_a_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2805_: u8 = 0;
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2809_: u8 = 0;
    let mut v_a_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v_a_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2825_: u8 = 0;
    let mut v_a_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2829_: u8 = 0;
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2701_ = lean_st_ref_get(v___y_2699_);
                v_env_2702_ = lean_ctor_get(v___x_2701_, 0);
                lean_inc_ref(v_env_2702_);
                lean_dec(v___x_2701_);
                v___x_2703_ = lean_st_ref_get(v___y_2699_);
                v_scopes_2704_ = lean_ctor_get(v___x_2703_, 2);
                lean_inc(v_scopes_2704_);
                lean_dec(v___x_2703_);
                v___x_2705_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_2706_ = l_List_head_x21___redArg(v___x_2705_, v_scopes_2704_);
                lean_dec(v_scopes_2704_);
                v_opts_2707_ = lean_ctor_get(v___x_2706_, 1);
                lean_inc_ref(v_opts_2707_);
                lean_dec(v___x_2706_);
                v___x_2708_ = l_Lean_Elab_Command_getScope___redArg(v___y_2699_);
                if lean_obj_tag(v___x_2708_) == 0 {
                    v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
                    lean_inc(v_a_2709_);
                    lean_dec_ref_known(v___x_2708_, 1);
                    v_currNamespace_2710_ = lean_ctor_get(v_a_2709_, 2);
                    lean_inc(v_currNamespace_2710_);
                    lean_dec(v_a_2709_);
                    v___x_2711_ = l_Lean_Elab_Command_getScope___redArg(v___y_2699_);
                    if lean_obj_tag(v___x_2711_) == 0 {
                        v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
                        lean_inc(v_a_2712_);
                        lean_dec_ref_known(v___x_2711_, 1);
                        v_openDecls_2713_ = lean_ctor_get(v_a_2712_, 3);
                        lean_inc(v_openDecls_2713_);
                        lean_dec(v_a_2712_);
                        v___x_2714_ = l_Lean_Elab_Command_getRef___redArg(v___y_2698_);
                        if lean_obj_tag(v___x_2714_) == 0 {
                            v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
                            lean_inc(v_a_2715_);
                            lean_dec_ref_known(v___x_2714_, 1);
                            v___x_2716_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2698_);
                            if lean_obj_tag(v___x_2716_) == 0 {
                                v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
                                lean_inc(v_a_2717_);
                                lean_dec_ref_known(v___x_2716_, 1);
                                v_currRecDepth_2718_ = lean_ctor_get(v___y_2698_, 2);
                                v_quotContext_x3f_2719_ = lean_ctor_get(v___y_2698_, 5);
                                lean_inc_ref_n(v_env_2702_, 3);
                                v___f_2720_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                                lean_closure_set(v___f_2720_, 0, v_env_2702_);
                                v___f_2721_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                                lean_closure_set(v___f_2721_, 0, v_env_2702_);
                                lean_inc_n(v_currNamespace_2710_, 2);
                                v___f_2722_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                                lean_closure_set(v___f_2722_, 0, v_currNamespace_2710_);
                                lean_inc(v_openDecls_2713_);
                                v___f_2723_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                                lean_closure_set(v___f_2723_, 0, v_env_2702_);
                                lean_closure_set(v___f_2723_, 1, v_currNamespace_2710_);
                                lean_closure_set(v___f_2723_, 2, v_openDecls_2713_);
                                v___f_2724_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                                lean_closure_set(v___f_2724_, 0, v_env_2702_);
                                lean_closure_set(v___f_2724_, 1, v_opts_2707_);
                                lean_closure_set(v___f_2724_, 2, v_currNamespace_2710_);
                                lean_closure_set(v___f_2724_, 3, v_openDecls_2713_);
                                v_methods_2725_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_methods_2725_, 0, v___f_2721_);
                                lean_ctor_set(v_methods_2725_, 1, v___f_2722_);
                                lean_ctor_set(v_methods_2725_, 2, v___f_2720_);
                                lean_ctor_set(v_methods_2725_, 3, v___f_2723_);
                                lean_ctor_set(v_methods_2725_, 4, v___f_2724_);
                                if lean_obj_tag(v_quotContext_x3f_2719_) == 0 {
                                    v___x_2799_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___redArg(v___y_2699_);
                                    v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
                                    lean_inc(v_a_2800_);
                                    lean_dec_ref(v___x_2799_);
                                    v_a_2727_ = v_a_2800_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_2801_ = lean_ctor_get(v_quotContext_x3f_2719_, 0);
                                    lean_inc(v_val_2801_);
                                    v_a_2727_ = v_val_2801_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_2715_);
                                lean_dec(v_openDecls_2713_);
                                lean_dec(v_currNamespace_2710_);
                                lean_dec_ref(v_opts_2707_);
                                lean_dec_ref(v_env_2702_);
                                lean_dec_ref(v_x_2697_);
                                v_a_2802_ = lean_ctor_get(v___x_2716_, 0);
                                v_isSharedCheck_2809_ = (!lean_is_exclusive(v___x_2716_)) as u8;
                                if v_isSharedCheck_2809_ == 0 {
                                    v___x_2804_ = v___x_2716_;
                                    v_isShared_2805_ = v_isSharedCheck_2809_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_2802_);
                                    lean_dec(v___x_2716_);
                                    v___x_2804_ = lean_box(0);
                                    v_isShared_2805_ = v_isSharedCheck_2809_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_openDecls_2713_);
                            lean_dec(v_currNamespace_2710_);
                            lean_dec_ref(v_opts_2707_);
                            lean_dec_ref(v_env_2702_);
                            lean_dec_ref(v_x_2697_);
                            v_a_2810_ = lean_ctor_get(v___x_2714_, 0);
                            v_isSharedCheck_2817_ = (!lean_is_exclusive(v___x_2714_)) as u8;
                            if v_isSharedCheck_2817_ == 0 {
                                v___x_2812_ = v___x_2714_;
                                v_isShared_2813_ = v_isSharedCheck_2817_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_2810_);
                                lean_dec(v___x_2714_);
                                v___x_2812_ = lean_box(0);
                                v_isShared_2813_ = v_isSharedCheck_2817_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_currNamespace_2710_);
                        lean_dec_ref(v_opts_2707_);
                        lean_dec_ref(v_env_2702_);
                        lean_dec_ref(v_x_2697_);
                        v_a_2818_ = lean_ctor_get(v___x_2711_, 0);
                        v_isSharedCheck_2825_ = (!lean_is_exclusive(v___x_2711_)) as u8;
                        if v_isSharedCheck_2825_ == 0 {
                            v___x_2820_ = v___x_2711_;
                            v_isShared_2821_ = v_isSharedCheck_2825_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2818_);
                            lean_dec(v___x_2711_);
                            v___x_2820_ = lean_box(0);
                            v_isShared_2821_ = v_isSharedCheck_2825_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_opts_2707_);
                    lean_dec_ref(v_env_2702_);
                    lean_dec_ref(v_x_2697_);
                    v_a_2826_ = lean_ctor_get(v___x_2708_, 0);
                    v_isSharedCheck_2833_ = (!lean_is_exclusive(v___x_2708_)) as u8;
                    if v_isSharedCheck_2833_ == 0 {
                        v___x_2828_ = v___x_2708_;
                        v_isShared_2829_ = v_isSharedCheck_2833_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2826_);
                        lean_dec(v___x_2708_);
                        v___x_2828_ = lean_box(0);
                        v_isShared_2829_ = v_isSharedCheck_2833_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2728_ = lean_st_ref_get(v___y_2699_);
                v_maxRecDepth_2729_ = lean_ctor_get(v___x_2728_, 5);
                lean_inc(v_maxRecDepth_2729_);
                lean_dec(v___x_2728_);
                v___x_2730_ = lean_st_ref_get(v___y_2699_);
                v_nextMacroScope_2731_ = lean_ctor_get(v___x_2730_, 4);
                lean_inc(v_nextMacroScope_2731_);
                lean_dec(v___x_2730_);
                lean_inc(v_currRecDepth_2718_);
                v___x_2732_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2732_, 0, v_methods_2725_);
                lean_ctor_set(v___x_2732_, 1, v_a_2727_);
                lean_ctor_set(v___x_2732_, 2, v_a_2717_);
                lean_ctor_set(v___x_2732_, 3, v_currRecDepth_2718_);
                lean_ctor_set(v___x_2732_, 4, v_maxRecDepth_2729_);
                lean_ctor_set(v___x_2732_, 5, v_a_2715_);
                v___x_2733_ = lean_box(0);
                v___x_2734_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2734_, 0, v_nextMacroScope_2731_);
                lean_ctor_set(v___x_2734_, 1, v___x_2733_);
                lean_ctor_set(v___x_2734_, 2, v___x_2733_);
                v___x_2735_ = lean_apply_2(v_x_2697_, v___x_2732_, v___x_2734_);
                if lean_obj_tag(v___x_2735_) == 0 {
                    v_a_2736_ = lean_ctor_get(v___x_2735_, 1);
                    lean_inc(v_a_2736_);
                    v_a_2737_ = lean_ctor_get(v___x_2735_, 0);
                    lean_inc(v_a_2737_);
                    lean_dec_ref_known(v___x_2735_, 2);
                    v_macroScope_2738_ = lean_ctor_get(v_a_2736_, 0);
                    lean_inc(v_macroScope_2738_);
                    v_traceMsgs_2739_ = lean_ctor_get(v_a_2736_, 1);
                    lean_inc(v_traceMsgs_2739_);
                    v_expandedMacroDecls_2740_ = lean_ctor_get(v_a_2736_, 2);
                    lean_inc(v_expandedMacroDecls_2740_);
                    lean_dec(v_a_2736_);
                    v___x_2741_ = lean_box(0);
                    v___x_2742_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4___redArg(v_expandedMacroDecls_2740_, v___x_2741_, v___y_2698_, v___y_2699_);
                    lean_dec(v_expandedMacroDecls_2740_);
                    if lean_obj_tag(v___x_2742_) == 0 {
                        lean_dec_ref_known(v___x_2742_, 1);
                        v___x_2743_ = lean_st_ref_take(v___y_2699_);
                        v_env_2744_ = lean_ctor_get(v___x_2743_, 0);
                        v_messages_2745_ = lean_ctor_get(v___x_2743_, 1);
                        v_scopes_2746_ = lean_ctor_get(v___x_2743_, 2);
                        v_usedQuotCtxts_2747_ = lean_ctor_get(v___x_2743_, 3);
                        v_maxRecDepth_2748_ = lean_ctor_get(v___x_2743_, 5);
                        v_ngen_2749_ = lean_ctor_get(v___x_2743_, 6);
                        v_auxDeclNGen_2750_ = lean_ctor_get(v___x_2743_, 7);
                        v_infoState_2751_ = lean_ctor_get(v___x_2743_, 8);
                        v_traceState_2752_ = lean_ctor_get(v___x_2743_, 9);
                        v_snapshotTasks_2753_ = lean_ctor_get(v___x_2743_, 10);
                        v_isSharedCheck_2779_ = (!lean_is_exclusive(v___x_2743_)) as u8;
                        if v_isSharedCheck_2779_ == 0 {
                            v_unused_2780_ = lean_ctor_get(v___x_2743_, 4);
                            lean_dec(v_unused_2780_);
                            v___x_2755_ = v___x_2743_;
                            v_isShared_2756_ = v_isSharedCheck_2779_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_2753_);
                            lean_inc(v_traceState_2752_);
                            lean_inc(v_infoState_2751_);
                            lean_inc(v_auxDeclNGen_2750_);
                            lean_inc(v_ngen_2749_);
                            lean_inc(v_maxRecDepth_2748_);
                            lean_inc(v_usedQuotCtxts_2747_);
                            lean_inc(v_scopes_2746_);
                            lean_inc(v_messages_2745_);
                            lean_inc(v_env_2744_);
                            lean_dec(v___x_2743_);
                            v___x_2755_ = lean_box(0);
                            v_isShared_2756_ = v_isSharedCheck_2779_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_traceMsgs_2739_);
                        lean_dec(v_macroScope_2738_);
                        lean_dec(v_a_2737_);
                        v_a_2781_ = lean_ctor_get(v___x_2742_, 0);
                        v_isSharedCheck_2788_ = (!lean_is_exclusive(v___x_2742_)) as u8;
                        if v_isSharedCheck_2788_ == 0 {
                            v___x_2783_ = v___x_2742_;
                            v_isShared_2784_ = v_isSharedCheck_2788_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2781_);
                            lean_dec(v___x_2742_);
                            v___x_2783_ = lean_box(0);
                            v_isShared_2784_ = v_isSharedCheck_2788_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_2789_ = lean_ctor_get(v___x_2735_, 0);
                    lean_inc(v_a_2789_);
                    lean_dec_ref_known(v___x_2735_, 2);
                    if lean_obj_tag(v_a_2789_) == 0 {
                        v_a_2790_ = lean_ctor_get(v_a_2789_, 0);
                        lean_inc(v_a_2790_);
                        v_a_2791_ = lean_ctor_get(v_a_2789_, 1);
                        lean_inc_ref(v_a_2791_);
                        lean_dec_ref_known(v_a_2789_, 2);
                        v___x_2792_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___closed__0;
                        v___x_2793_ = lean_string_dec_eq(v_a_2791_, v___x_2792_);
                        if v___x_2793_ == 0 {
                            v___x_2794_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_2794_, 0, v_a_2791_);
                            v___x_2795_ = l_Lean_MessageData_ofFormat(v___x_2794_);
                            v___x_2796_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6___redArg(v_a_2790_, v___x_2795_, v___y_2698_, v___y_2699_);
                            lean_dec(v_a_2790_);
                            return v___x_2796_;
                        } else {
                            lean_dec_ref(v_a_2791_);
                            v___x_2797_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg(v_a_2790_);
                            return v___x_2797_;
                        }
                    } else {
                        v___x_2798_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                        return v___x_2798_;
                    }
                }
            }
            2 => {
                if v_isShared_2756_ == 0 {
                    lean_ctor_set(v___x_2755_, 4, v_macroScope_2738_);
                    v___x_2758_ = v___x_2755_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_env_2744_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_messages_2745_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_scopes_2746_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_usedQuotCtxts_2747_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 4, v_macroScope_2738_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 5, v_maxRecDepth_2748_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_ngen_2749_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 7, v_auxDeclNGen_2750_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 8, v_infoState_2751_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 9, v_traceState_2752_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 10, v_snapshotTasks_2753_);
                    v___x_2758_ = v_reuseFailAlloc_2778_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2759_ = lean_st_ref_set(v___y_2699_, v___x_2758_);
                v___x_2760_ = l_List_reverse___redArg(v_traceMsgs_2739_);
                v___x_2761_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__5(v___x_2760_, v___y_2698_, v___y_2699_);
                if lean_obj_tag(v___x_2761_) == 0 {
                    v_isSharedCheck_2768_ = (!lean_is_exclusive(v___x_2761_)) as u8;
                    if v_isSharedCheck_2768_ == 0 {
                        v_unused_2769_ = lean_ctor_get(v___x_2761_, 0);
                        lean_dec(v_unused_2769_);
                        v___x_2763_ = v___x_2761_;
                        v_isShared_2764_ = v_isSharedCheck_2768_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_2761_);
                        v___x_2763_ = lean_box(0);
                        v_isShared_2764_ = v_isSharedCheck_2768_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2737_);
                    v_a_2770_ = lean_ctor_get(v___x_2761_, 0);
                    v_isSharedCheck_2777_ = (!lean_is_exclusive(v___x_2761_)) as u8;
                    if v_isSharedCheck_2777_ == 0 {
                        v___x_2772_ = v___x_2761_;
                        v_isShared_2773_ = v_isSharedCheck_2777_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2770_);
                        lean_dec(v___x_2761_);
                        v___x_2772_ = lean_box(0);
                        v_isShared_2773_ = v_isSharedCheck_2777_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2764_ == 0 {
                    lean_ctor_set(v___x_2763_, 0, v_a_2737_);
                    v___x_2766_ = v___x_2763_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2737_);
                    v___x_2766_ = v_reuseFailAlloc_2767_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2766_;
            }
            6 => {
                if v_isShared_2773_ == 0 {
                    v___x_2775_ = v___x_2772_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
                    v___x_2775_ = v_reuseFailAlloc_2776_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2775_;
            }
            8 => {
                if v_isShared_2784_ == 0 {
                    v___x_2786_ = v___x_2783_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
                    v___x_2786_ = v_reuseFailAlloc_2787_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2786_;
            }
            10 => {
                if v_isShared_2805_ == 0 {
                    v___x_2807_ = v___x_2804_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
                    v___x_2807_ = v_reuseFailAlloc_2808_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2807_;
            }
            12 => {
                if v_isShared_2813_ == 0 {
                    v___x_2815_ = v___x_2812_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2815_;
            }
            14 => {
                if v_isShared_2821_ == 0 {
                    v___x_2823_ = v___x_2820_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
                    v___x_2823_ = v_reuseFailAlloc_2824_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2823_;
            }
            16 => {
                if v_isShared_2829_ == 0 {
                    v___x_2831_ = v___x_2828_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
                    v___x_2831_ = v_reuseFailAlloc_2832_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg___boxed(
    mut v_x_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2838_: *mut LeanObject = core::ptr::null_mut();
    v_res_2838_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg(
        v_x_2834_,
        v___y_2835_,
        v___y_2836_,
    );
    lean_dec(v___y_2836_);
    lean_dec_ref(v___y_2835_);
    return v_res_2838_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabBinderPred___closed__32() -> *mut LeanObject {
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    v___x_2888_ = l_Lean_Elab_Command_elabBinderPred___closed__31;
    v___x_2889_ = l_String_toRawSubstring_x27(v___x_2888_);
    return v___x_2889_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabBinderPred___closed__47() -> *mut LeanObject {
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    v___x_2919_ = l_Array_mkArray0(lean_box(0));
    return v___x_2919_;
}
pub unsafe fn l_Lean_Elab_Command_elabBinderPred(
    mut v_stx_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3035_: u8 = 0;
    let mut v___y_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3055_: usize = 0;
    let mut v___y_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3076_: usize = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3112_: u8 = 0;
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_a_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_a_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v___y_3134_: u8 = 0;
    let mut v___y_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: usize = 0;
    let mut v___y_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3179_: u8 = 0;
    let mut v___y_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3199_: usize = 0;
    let mut v___y_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3219_: u8 = 0;
    let mut v___y_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3229_: usize = 0;
    let mut v___y_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3262_: usize = 0;
    let mut v___x_3263_: usize = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v_a_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3299_: u8 = 0;
    let mut v_a_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3303_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v_a_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3311_: u8 = 0;
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3315_: u8 = 0;
    let mut v___y_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: u8 = 0;
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: u8 = 0;
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: u8 = 0;
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2943_ = l_Lean_Elab_Command_elabBinderPred___closed__0;
                v___x_2944_ = l_Lean_Elab_Command_elabBinderPred___closed__1;
                v___x_3007_ = l_Lean_Elab_Command_elabBinderPred___closed__20;
                lean_inc(v_stx_2939_);
                v___x_3008_ = l_Lean_Syntax_isOfKind(v_stx_2939_, v___x_3007_);
                if v___x_3008_ == 0 {
                    lean_dec(v_stx_2939_);
                    v___x_3009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                    return v___x_3009_;
                } else {
                    v___x_3010_ = lean_unsigned_to_nat(0);
                    v___x_3386_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3010_);
                    v___x_3387_ = l_Lean_Syntax_isNone(v___x_3386_);
                    if v___x_3387_ == 0 {
                        v___x_3388_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3386_);
                        v___x_3389_ = l_Lean_Syntax_matchesNull(v___x_3386_, v___x_3388_);
                        if v___x_3389_ == 0 {
                            lean_dec(v___x_3386_);
                            lean_dec(v_stx_2939_);
                            v___x_3390_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                            return v___x_3390_;
                        } else {
                            v_doc_x3f_3391_ = l_Lean_Syntax_getArg(v___x_3386_, v___x_3010_);
                            lean_dec(v___x_3386_);
                            v___x_3392_ = l_Lean_Elab_Command_elabBinderPred___closed__54;
                            lean_inc(v_doc_x3f_3391_);
                            v___x_3393_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3391_, v___x_3392_);
                            if v___x_3393_ == 0 {
                                lean_dec(v_doc_x3f_3391_);
                                lean_dec(v_stx_2939_);
                                v___x_3394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                                return v___x_3394_;
                            } else {
                                v___x_3395_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3395_, 0, v_doc_x3f_3391_);
                                v_doc_x3f_3370_ = v___x_3395_;
                                v___y_3371_ = v_a_2940_;
                                v___y_3372_ = v_a_2941_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3386_);
                        v___x_3396_ = lean_box(0);
                        v_doc_x3f_3370_ = v___x_3396_;
                        v___y_3371_ = v_a_2940_;
                        v___y_3372_ = v_a_2941_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_2951_, 2);
                v___x_2964_ = l_Array_append___redArg(v___y_2951_, v___y_2963_);
                lean_dec_ref(v___y_2963_);
                lean_inc_n(v___y_2958_, 5);
                lean_inc_n(v___y_2952_, 22);
                v___x_2965_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2965_, 0, v___y_2952_);
                lean_ctor_set(v___x_2965_, 1, v___y_2958_);
                lean_ctor_set(v___x_2965_, 2, v___x_2964_);
                v___x_2966_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2966_, 0, v___y_2952_);
                lean_ctor_set(v___x_2966_, 1, v___y_2958_);
                lean_ctor_set(v___x_2966_, 2, v___y_2951_);
                lean_inc_ref_n(v___x_2966_, 3);
                lean_inc(v___y_2959_);
                v___x_2967_ = l_Lean_Syntax_node1(v___y_2952_, v___y_2959_, v___x_2966_);
                lean_inc_ref(v___y_2953_);
                v___x_2968_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2968_, 0, v___y_2956_);
                lean_ctor_set(v___x_2968_, 1, v___y_2953_);
                v___x_2969_ = l_Lean_Elab_Command_elabBinderPred___closed__2;
                lean_inc_ref_n(v___y_2957_, 3);
                v___x_2970_ =
                    l_Lean_Name_mkStr4(v___x_2943_, v___x_2944_, v___y_2957_, v___x_2969_);
                v___x_2971_ = l_Lean_Elab_Command_elabBinderPred___closed__3;
                v___x_2972_ =
                    l_Lean_Name_mkStr4(v___x_2943_, v___x_2944_, v___y_2957_, v___x_2971_);
                v___x_2973_ = l_Lean_Elab_Command_elabBinderPred___closed__4;
                v___x_2974_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2974_, 0, v___y_2952_);
                lean_ctor_set(v___x_2974_, 1, v___x_2973_);
                v___x_2975_ = l_Lean_Elab_Command_elabBinderPred___closed__5;
                v___x_2976_ =
                    l_Lean_Name_mkStr4(v___x_2943_, v___x_2944_, v___y_2957_, v___x_2975_);
                v___x_2977_ = l_Lean_Elab_Command_elabBinderPred___closed__6;
                v___x_2978_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2978_, 0, v___y_2952_);
                lean_ctor_set(v___x_2978_, 1, v___x_2977_);
                v___x_2979_ = l_Lean_Elab_Command_elabBinderPred___closed__8;
                v___x_2980_ = l_Lean_Elab_Command_elabBinderPred___closed__9;
                v___x_2981_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2981_, 0, v___y_2952_);
                lean_ctor_set(v___x_2981_, 1, v___x_2980_);
                v___x_2982_ = l_Lean_Elab_Command_elabBinderPred___closed__10;
                v___x_2983_ = l_Lean_Elab_Command_elabBinderPred___closed__11;
                lean_inc_ref_n(v___y_2950_, 2);
                v___x_2984_ = l_Lean_Name_mkStr3(v___y_2950_, v___x_2982_, v___x_2983_);
                v___x_2985_ = l_Lean_Elab_Command_elabBinderPred___closed__12;
                v___x_2986_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2986_, 0, v___y_2952_);
                lean_ctor_set(v___x_2986_, 1, v___x_2985_);
                v___x_2987_ = l_Lean_Elab_Command_elabBinderPred___closed__14;
                lean_inc_ref(v___y_2946_);
                v___x_2988_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2988_, 0, v___y_2952_);
                lean_ctor_set(v___x_2988_, 1, v___y_2946_);
                lean_inc_ref(v___y_2955_);
                v___x_2989_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2989_, 0, v___y_2952_);
                lean_ctor_set(v___x_2989_, 1, v___y_2955_);
                lean_inc_ref(v___x_2989_);
                v___x_2990_ = l_Lean_Syntax_node3(
                    v___y_2952_,
                    v___x_2987_,
                    v___x_2988_,
                    v___y_2960_,
                    v___x_2989_,
                );
                v___x_2991_ = l_Lean_Elab_Command_elabBinderPred___closed__16;
                lean_inc_ref(v___y_2961_);
                v___x_2992_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2992_, 0, v___y_2952_);
                lean_ctor_set(v___x_2992_, 1, v___y_2961_);
                v___x_2993_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2993_, 0, v___y_2952_);
                lean_ctor_set(v___x_2993_, 1, v___y_2950_);
                v___x_2994_ =
                    l_Lean_Syntax_node2(v___y_2952_, v___x_2991_, v___x_2992_, v___x_2993_);
                v___x_2995_ = l_Lean_Syntax_node4(
                    v___y_2952_,
                    v___x_2984_,
                    v___x_2986_,
                    v___x_2966_,
                    v___x_2990_,
                    v___x_2994_,
                );
                v___x_2996_ = l_Lean_Syntax_node3(
                    v___y_2952_,
                    v___x_2979_,
                    v___x_2981_,
                    v___x_2995_,
                    v___y_2962_,
                );
                v___x_2997_ = l_Lean_Syntax_node3(
                    v___y_2952_,
                    v___x_2976_,
                    v___x_2978_,
                    v___x_2996_,
                    v___x_2989_,
                );
                v___x_2998_ = l_Lean_Syntax_node1(v___y_2952_, v___y_2958_, v___x_2997_);
                v___x_2999_ = l_Lean_Syntax_node1(v___y_2952_, v___y_2958_, v___x_2998_);
                v___x_3000_ = l_Lean_Elab_Command_elabBinderPred___closed__17;
                v___x_3001_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3001_, 0, v___y_2952_);
                lean_ctor_set(v___x_3001_, 1, v___x_3000_);
                v___x_3002_ = l_Lean_Syntax_node4(
                    v___y_2952_,
                    v___x_2972_,
                    v___x_2974_,
                    v___x_2999_,
                    v___x_3001_,
                    v___y_2948_,
                );
                v___x_3003_ = l_Lean_Syntax_node1(v___y_2952_, v___y_2958_, v___x_3002_);
                v___x_3004_ = l_Lean_Syntax_node1(v___y_2952_, v___x_2970_, v___x_3003_);
                lean_inc(v___y_2949_);
                v___x_3005_ = l_Lean_Syntax_node6(
                    v___y_2952_,
                    v___y_2949_,
                    v___x_2965_,
                    v___x_2966_,
                    v___x_2967_,
                    v___x_2968_,
                    v___x_2966_,
                    v___x_3004_,
                );
                v___x_3006_ =
                    l_Lean_Elab_Command_elabCommand(v___x_3005_, v___y_2954_, v___y_2947_);
                return v___x_3006_;
            }
            2 => {
                v___x_3028_ = l_Lean_Elab_Command_elabBinderPred___closed__21;
                v___x_3029_ = l_Lean_Elab_Command_elabBinderPred___closed__22;
                if lean_obj_tag(v___y_3025_) == 1 {
                    v_val_3030_ = lean_ctor_get(v___y_3025_, 0);
                    lean_inc(v_val_3030_);
                    lean_dec_ref_known(v___y_3025_, 1);
                    v___x_3031_ = l_Array_mkArray1___redArg(v_val_3030_);
                    v___y_2946_ = v___y_3012_;
                    v___y_2947_ = v___y_3013_;
                    v___y_2948_ = v___y_3014_;
                    v___y_2949_ = v___x_3029_;
                    v___y_2950_ = v___y_3015_;
                    v___y_2951_ = v___y_3016_;
                    v___y_2952_ = v___y_3017_;
                    v___y_2953_ = v___x_3028_;
                    v___y_2954_ = v___y_3018_;
                    v___y_2955_ = v___y_3019_;
                    v___y_2956_ = v___y_3020_;
                    v___y_2957_ = v___y_3021_;
                    v___y_2958_ = v___y_3022_;
                    v___y_2959_ = v___y_3023_;
                    v___y_2960_ = v___y_3024_;
                    v___y_2961_ = v___y_3027_;
                    v___y_2962_ = v___y_3026_;
                    v___y_2963_ = v___x_3031_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_3025_);
                    v___x_3032_ = l_Lean_Elab_Command_elabBinderPred___closed__23;
                    v___y_2946_ = v___y_3012_;
                    v___y_2947_ = v___y_3013_;
                    v___y_2948_ = v___y_3014_;
                    v___y_2949_ = v___x_3029_;
                    v___y_2950_ = v___y_3015_;
                    v___y_2951_ = v___y_3016_;
                    v___y_2952_ = v___y_3017_;
                    v___y_2953_ = v___x_3028_;
                    v___y_2954_ = v___y_3018_;
                    v___y_2955_ = v___y_3019_;
                    v___y_2956_ = v___y_3020_;
                    v___y_2957_ = v___y_3021_;
                    v___y_2958_ = v___y_3022_;
                    v___y_2959_ = v___y_3023_;
                    v___y_2960_ = v___y_3024_;
                    v___y_2961_ = v___y_3027_;
                    v___y_2962_ = v___y_3026_;
                    v___y_2963_ = v___x_3032_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc_ref_n(v___y_3041_, 2);
                v___x_3060_ = l_Array_append___redArg(v___y_3041_, v___y_3059_);
                lean_dec_ref(v___y_3059_);
                lean_inc_n(v___y_3046_, 3);
                lean_inc_n(v___y_3042_, 10);
                v___x_3061_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3061_, 0, v___y_3042_);
                lean_ctor_set(v___x_3061_, 1, v___y_3046_);
                lean_ctor_set(v___x_3061_, 2, v___x_3060_);
                v___x_3062_ = l_Lean_Elab_Command_elabBinderPred___closed__25;
                v___x_3063_ = l_Lean_Elab_Command_elabBinderPred___closed__26;
                v___x_3064_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3064_, 0, v___y_3042_);
                lean_ctor_set(v___x_3064_, 1, v___x_3063_);
                v___x_3065_ = l_Lean_Elab_Command_elabBinderPred___closed__27;
                v___x_3066_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3066_, 0, v___y_3042_);
                lean_ctor_set(v___x_3066_, 1, v___x_3065_);
                v___x_3067_ = l_Lean_Elab_Command_elabBinderPred___closed__28;
                v___x_3068_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3068_, 0, v___y_3042_);
                lean_ctor_set(v___x_3068_, 1, v___x_3067_);
                v___x_3069_ = l_Nat_reprFast(v___y_3034_);
                v___x_3070_ = lean_box(2);
                v___x_3071_ = l_Lean_Syntax_mkNumLit(v___x_3069_, v___x_3070_);
                v___x_3072_ = l_Lean_Elab_Command_elabBinderPred___closed__29;
                v___x_3073_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3073_, 0, v___y_3042_);
                lean_ctor_set(v___x_3073_, 1, v___x_3072_);
                v___x_3074_ = l_Lean_Syntax_node5(
                    v___y_3042_,
                    v___x_3062_,
                    v___x_3064_,
                    v___x_3066_,
                    v___x_3068_,
                    v___x_3071_,
                    v___x_3073_,
                );
                v___x_3075_ = l_Lean_Syntax_node1(v___y_3042_, v___y_3046_, v___x_3074_);
                v_sz_3076_ = lean_array_size(v___y_3053_);
                v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__3(v_sz_3076_, v___y_3055_, v___y_3053_);
                v___x_3078_ = l_Array_append___redArg(v___y_3041_, v___x_3077_);
                lean_dec_ref(v___x_3077_);
                v___x_3079_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3079_, 0, v___y_3042_);
                lean_ctor_set(v___x_3079_, 1, v___y_3046_);
                lean_ctor_set(v___x_3079_, 2, v___x_3078_);
                v___x_3080_ = l_Lean_Elab_Command_elabBinderPred___closed__30;
                v___x_3081_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3081_, 0, v___y_3042_);
                lean_ctor_set(v___x_3081_, 1, v___x_3080_);
                v___x_3082_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabBinderPred___closed__32),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabBinderPred___closed__32_once),
                    _init_l_Lean_Elab_Command_elabBinderPred___closed__32,
                );
                v___x_3083_ = l_Lean_Elab_Command_elabBinderPred___closed__33;
                v___x_3084_ = l_Lean_addMacroScope(v___y_3044_, v___x_3083_, v___y_3037_);
                v___x_3085_ = l_Lean_Elab_Command_elabBinderPred___closed__36;
                v___x_3086_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3086_, 0, v___y_3042_);
                lean_ctor_set(v___x_3086_, 1, v___x_3082_);
                lean_ctor_set(v___x_3086_, 2, v___x_3084_);
                lean_ctor_set(v___x_3086_, 3, v___x_3085_);
                v___x_3087_ = lean_unsigned_to_nat(10);
                v___x_3088_ = lean_mk_empty_array_with_capacity(v___x_3087_);
                v___x_3089_ = lean_array_push(v___x_3088_, v___y_3057_);
                v___x_3090_ = lean_array_push(v___x_3089_, v___y_3058_);
                v___x_3091_ = lean_array_push(v___x_3090_, v___y_3040_);
                v___x_3092_ = lean_array_push(v___x_3091_, v___y_3036_);
                v___x_3093_ = lean_array_push(v___x_3092_, v___y_3048_);
                v___x_3094_ = lean_array_push(v___x_3093_, v___x_3061_);
                v___x_3095_ = lean_array_push(v___x_3094_, v___x_3075_);
                v___x_3096_ = lean_array_push(v___x_3095_, v___x_3079_);
                v___x_3097_ = lean_array_push(v___x_3096_, v___x_3081_);
                v___x_3098_ = lean_array_push(v___x_3097_, v___x_3086_);
                lean_inc(v___y_3038_);
                v___x_3099_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3099_, 0, v___y_3042_);
                lean_ctor_set(v___x_3099_, 1, v___y_3038_);
                lean_ctor_set(v___x_3099_, 2, v___x_3098_);
                v___x_3100_ = l_Lean_Elab_Command_elabSyntax(v___x_3099_, v___y_3056_, v___y_3052_);
                if lean_obj_tag(v___x_3100_) == 0 {
                    v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
                    lean_inc(v_a_3101_);
                    lean_dec_ref_known(v___x_3100_, 1);
                    v___x_3102_ = l_Lean_Elab_Command_getRef___redArg(v___y_3056_);
                    if lean_obj_tag(v___x_3102_) == 0 {
                        v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
                        lean_inc(v_a_3103_);
                        lean_dec_ref_known(v___x_3102_, 1);
                        v___x_3104_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3056_);
                        if lean_obj_tag(v___x_3104_) == 0 {
                            lean_dec_ref_known(v___x_3104_, 1);
                            v_quotContext_x3f_3105_ = lean_ctor_get(v___y_3056_, 5);
                            v___x_3106_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_3106_, 0, v___x_3070_);
                            lean_ctor_set(v___x_3106_, 1, v_a_3101_);
                            lean_ctor_set(v___x_3106_, 2, v___y_3051_);
                            v___x_3107_ = l_Lean_SourceInfo_fromRef(v_a_3103_, v___y_3035_);
                            lean_dec(v_a_3103_);
                            if lean_obj_tag(v_quotContext_x3f_3105_) == 0 {
                                v___x_3108_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___redArg(v___y_3052_);
                                lean_dec_ref(v___x_3108_);
                                v___y_3012_ = v___x_3063_;
                                v___y_3013_ = v___y_3052_;
                                v___y_3014_ = v___y_3039_;
                                v___y_3015_ = v___y_3054_;
                                v___y_3016_ = v___y_3041_;
                                v___y_3017_ = v___x_3107_;
                                v___y_3018_ = v___y_3056_;
                                v___y_3019_ = v___x_3072_;
                                v___y_3020_ = v___y_3043_;
                                v___y_3021_ = v___y_3045_;
                                v___y_3022_ = v___y_3046_;
                                v___y_3023_ = v___y_3047_;
                                v___y_3024_ = v___y_3049_;
                                v___y_3025_ = v___y_3050_;
                                v___y_3026_ = v___x_3106_;
                                v___y_3027_ = v___x_3080_;
                                state = 2;
                                continue;
                            } else {
                                v___y_3012_ = v___x_3063_;
                                v___y_3013_ = v___y_3052_;
                                v___y_3014_ = v___y_3039_;
                                v___y_3015_ = v___y_3054_;
                                v___y_3016_ = v___y_3041_;
                                v___y_3017_ = v___x_3107_;
                                v___y_3018_ = v___y_3056_;
                                v___y_3019_ = v___x_3072_;
                                v___y_3020_ = v___y_3043_;
                                v___y_3021_ = v___y_3045_;
                                v___y_3022_ = v___y_3046_;
                                v___y_3023_ = v___y_3047_;
                                v___y_3024_ = v___y_3049_;
                                v___y_3025_ = v___y_3050_;
                                v___y_3026_ = v___x_3106_;
                                v___y_3027_ = v___x_3080_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3103_);
                            lean_dec(v_a_3101_);
                            lean_dec_ref(v___y_3051_);
                            lean_dec(v___y_3050_);
                            lean_dec(v___y_3049_);
                            lean_dec(v___y_3043_);
                            lean_dec(v___y_3039_);
                            v_a_3109_ = lean_ctor_get(v___x_3104_, 0);
                            v_isSharedCheck_3116_ = (!lean_is_exclusive(v___x_3104_)) as u8;
                            if v_isSharedCheck_3116_ == 0 {
                                v___x_3111_ = v___x_3104_;
                                v_isShared_3112_ = v_isSharedCheck_3116_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3109_);
                                lean_dec(v___x_3104_);
                                v___x_3111_ = lean_box(0);
                                v_isShared_3112_ = v_isSharedCheck_3116_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3101_);
                        lean_dec_ref(v___y_3051_);
                        lean_dec(v___y_3050_);
                        lean_dec(v___y_3049_);
                        lean_dec(v___y_3043_);
                        lean_dec(v___y_3039_);
                        v_a_3117_ = lean_ctor_get(v___x_3102_, 0);
                        v_isSharedCheck_3124_ = (!lean_is_exclusive(v___x_3102_)) as u8;
                        if v_isSharedCheck_3124_ == 0 {
                            v___x_3119_ = v___x_3102_;
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3117_);
                            lean_dec(v___x_3102_);
                            v___x_3119_ = lean_box(0);
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3051_);
                    lean_dec(v___y_3050_);
                    lean_dec(v___y_3049_);
                    lean_dec(v___y_3043_);
                    lean_dec(v___y_3039_);
                    v_a_3125_ = lean_ctor_get(v___x_3100_, 0);
                    v_isSharedCheck_3132_ = (!lean_is_exclusive(v___x_3100_)) as u8;
                    if v_isSharedCheck_3132_ == 0 {
                        v___x_3127_ = v___x_3100_;
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3125_);
                        lean_dec(v___x_3100_);
                        v___x_3127_ = lean_box(0);
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3112_ == 0 {
                    v___x_3114_ = v___x_3111_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3114_;
            }
            6 => {
                if v_isShared_3120_ == 0 {
                    v___x_3122_ = v___x_3119_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3122_;
            }
            8 => {
                if v_isShared_3128_ == 0 {
                    v___x_3130_ = v___x_3127_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3130_;
            }
            10 => {
                lean_inc_ref_n(v___y_3142_, 2);
                v___x_3159_ = l_Array_append___redArg(v___y_3142_, v___y_3158_);
                lean_dec_ref(v___y_3158_);
                lean_inc_n(v___y_3146_, 2);
                lean_inc_n(v___y_3143_, 2);
                v___x_3160_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3160_, 0, v___y_3143_);
                lean_ctor_set(v___x_3160_, 1, v___y_3146_);
                lean_ctor_set(v___x_3160_, 2, v___x_3159_);
                v___x_3161_ = l_Lean_SourceInfo_fromRef(v___y_3136_, v___x_3008_);
                lean_dec(v___y_3136_);
                lean_inc_ref(v___y_3141_);
                lean_inc(v___x_3161_);
                v___x_3162_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3162_, 0, v___x_3161_);
                lean_ctor_set(v___x_3162_, 1, v___y_3141_);
                v___x_3163_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3163_, 0, v___y_3143_);
                lean_ctor_set(v___x_3163_, 1, v___y_3146_);
                lean_ctor_set(v___x_3163_, 2, v___y_3142_);
                if lean_obj_tag(v___y_3157_) == 1 {
                    v_val_3164_ = lean_ctor_get(v___y_3157_, 0);
                    lean_inc(v_val_3164_);
                    lean_dec_ref_known(v___y_3157_, 1);
                    v___x_3165_ = l_Lean_Elab_Command_elabBinderPred___closed__38;
                    v___x_3166_ = l_Lean_Elab_Command_elabBinderPred___closed__26;
                    lean_inc_n(v___y_3143_, 5);
                    v___x_3167_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3167_, 0, v___y_3143_);
                    lean_ctor_set(v___x_3167_, 1, v___x_3166_);
                    v___x_3168_ = l_Lean_Elab_Command_elabBinderPred___closed__39;
                    v___x_3169_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3169_, 0, v___y_3143_);
                    lean_ctor_set(v___x_3169_, 1, v___x_3168_);
                    v___x_3170_ = l_Lean_Elab_Command_elabBinderPred___closed__28;
                    v___x_3171_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3171_, 0, v___y_3143_);
                    lean_ctor_set(v___x_3171_, 1, v___x_3170_);
                    v___x_3172_ = l_Lean_Elab_Command_elabBinderPred___closed__29;
                    v___x_3173_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3173_, 0, v___y_3143_);
                    lean_ctor_set(v___x_3173_, 1, v___x_3172_);
                    v___x_3174_ = l_Lean_Syntax_node5(
                        v___y_3143_,
                        v___x_3165_,
                        v___x_3167_,
                        v___x_3169_,
                        v___x_3171_,
                        v_val_3164_,
                        v___x_3173_,
                    );
                    v___x_3175_ = l_Array_mkArray1___redArg(v___x_3174_);
                    v___y_3034_ = v___y_3135_;
                    v___y_3035_ = v___y_3134_;
                    v___y_3036_ = v___x_3162_;
                    v___y_3037_ = v___y_3137_;
                    v___y_3038_ = v___y_3139_;
                    v___y_3039_ = v___y_3138_;
                    v___y_3040_ = v___y_3140_;
                    v___y_3041_ = v___y_3142_;
                    v___y_3042_ = v___y_3143_;
                    v___y_3043_ = v___x_3161_;
                    v___y_3044_ = v___y_3144_;
                    v___y_3045_ = v___y_3145_;
                    v___y_3046_ = v___y_3146_;
                    v___y_3047_ = v___y_3147_;
                    v___y_3048_ = v___x_3163_;
                    v___y_3049_ = v___y_3148_;
                    v___y_3050_ = v___y_3149_;
                    v___y_3051_ = v___y_3150_;
                    v___y_3052_ = v___y_3151_;
                    v___y_3053_ = v___y_3152_;
                    v___y_3054_ = v___y_3153_;
                    v___y_3055_ = v___y_3154_;
                    v___y_3056_ = v___y_3155_;
                    v___y_3057_ = v___y_3156_;
                    v___y_3058_ = v___x_3160_;
                    v___y_3059_ = v___x_3175_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___y_3157_);
                    v___x_3176_ = l_Lean_Elab_Command_elabBinderPred___closed__23;
                    v___y_3034_ = v___y_3135_;
                    v___y_3035_ = v___y_3134_;
                    v___y_3036_ = v___x_3162_;
                    v___y_3037_ = v___y_3137_;
                    v___y_3038_ = v___y_3139_;
                    v___y_3039_ = v___y_3138_;
                    v___y_3040_ = v___y_3140_;
                    v___y_3041_ = v___y_3142_;
                    v___y_3042_ = v___y_3143_;
                    v___y_3043_ = v___x_3161_;
                    v___y_3044_ = v___y_3144_;
                    v___y_3045_ = v___y_3145_;
                    v___y_3046_ = v___y_3146_;
                    v___y_3047_ = v___y_3147_;
                    v___y_3048_ = v___x_3163_;
                    v___y_3049_ = v___y_3148_;
                    v___y_3050_ = v___y_3149_;
                    v___y_3051_ = v___y_3150_;
                    v___y_3052_ = v___y_3151_;
                    v___y_3053_ = v___y_3152_;
                    v___y_3054_ = v___y_3153_;
                    v___y_3055_ = v___y_3154_;
                    v___y_3056_ = v___y_3155_;
                    v___y_3057_ = v___y_3156_;
                    v___y_3058_ = v___x_3160_;
                    v___y_3059_ = v___x_3176_;
                    state = 3;
                    continue;
                }
            }
            11 => {
                lean_inc_ref(v___y_3187_);
                v___x_3203_ = l_Array_append___redArg(v___y_3187_, v___y_3202_);
                lean_dec_ref(v___y_3202_);
                lean_inc(v___y_3191_);
                lean_inc(v___y_3188_);
                v___x_3204_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3204_, 0, v___y_3188_);
                lean_ctor_set(v___x_3204_, 1, v___y_3191_);
                lean_ctor_set(v___x_3204_, 2, v___x_3203_);
                if lean_obj_tag(v___y_3180_) == 1 {
                    v_val_3205_ = lean_ctor_get(v___y_3180_, 0);
                    lean_inc(v_val_3205_);
                    lean_dec_ref_known(v___y_3180_, 1);
                    v___x_3206_ = l_Lean_Elab_Command_elabBinderPred___closed__40;
                    lean_inc_ref(v___y_3190_);
                    v___x_3207_ =
                        l_Lean_Name_mkStr4(v___x_2943_, v___x_2944_, v___y_3190_, v___x_3206_);
                    v___x_3208_ = l_Lean_Elab_Command_elabBinderPred___closed__41;
                    lean_inc_n(v___y_3188_, 4);
                    v___x_3209_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3209_, 0, v___y_3188_);
                    lean_ctor_set(v___x_3209_, 1, v___x_3208_);
                    lean_inc_ref(v___y_3187_);
                    v___x_3210_ = l_Array_append___redArg(v___y_3187_, v_val_3205_);
                    lean_dec(v_val_3205_);
                    lean_inc(v___y_3191_);
                    v___x_3211_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3211_, 0, v___y_3188_);
                    lean_ctor_set(v___x_3211_, 1, v___y_3191_);
                    lean_ctor_set(v___x_3211_, 2, v___x_3210_);
                    v___x_3212_ = l_Lean_Elab_Command_elabBinderPred___closed__42;
                    v___x_3213_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3213_, 0, v___y_3188_);
                    lean_ctor_set(v___x_3213_, 1, v___x_3212_);
                    v___x_3214_ = l_Lean_Syntax_node3(
                        v___y_3188_,
                        v___x_3207_,
                        v___x_3209_,
                        v___x_3211_,
                        v___x_3213_,
                    );
                    v___x_3215_ = l_Array_mkArray1___redArg(v___x_3214_);
                    v___y_3134_ = v___y_3179_;
                    v___y_3135_ = v___y_3178_;
                    v___y_3136_ = v___y_3181_;
                    v___y_3137_ = v___y_3182_;
                    v___y_3138_ = v___y_3184_;
                    v___y_3139_ = v___y_3183_;
                    v___y_3140_ = v___y_3186_;
                    v___y_3141_ = v___y_3185_;
                    v___y_3142_ = v___y_3187_;
                    v___y_3143_ = v___y_3188_;
                    v___y_3144_ = v___y_3189_;
                    v___y_3145_ = v___y_3190_;
                    v___y_3146_ = v___y_3191_;
                    v___y_3147_ = v___y_3192_;
                    v___y_3148_ = v___y_3193_;
                    v___y_3149_ = v___y_3194_;
                    v___y_3150_ = v___y_3195_;
                    v___y_3151_ = v___y_3196_;
                    v___y_3152_ = v___y_3197_;
                    v___y_3153_ = v___y_3198_;
                    v___y_3154_ = v___y_3199_;
                    v___y_3155_ = v___y_3200_;
                    v___y_3156_ = v___x_3204_;
                    v___y_3157_ = v___y_3201_;
                    v___y_3158_ = v___x_3215_;
                    state = 10;
                    continue;
                } else {
                    lean_dec(v___y_3180_);
                    v___x_3216_ = l_Lean_Elab_Command_elabBinderPred___closed__23;
                    v___y_3134_ = v___y_3179_;
                    v___y_3135_ = v___y_3178_;
                    v___y_3136_ = v___y_3181_;
                    v___y_3137_ = v___y_3182_;
                    v___y_3138_ = v___y_3184_;
                    v___y_3139_ = v___y_3183_;
                    v___y_3140_ = v___y_3186_;
                    v___y_3141_ = v___y_3185_;
                    v___y_3142_ = v___y_3187_;
                    v___y_3143_ = v___y_3188_;
                    v___y_3144_ = v___y_3189_;
                    v___y_3145_ = v___y_3190_;
                    v___y_3146_ = v___y_3191_;
                    v___y_3147_ = v___y_3192_;
                    v___y_3148_ = v___y_3193_;
                    v___y_3149_ = v___y_3194_;
                    v___y_3150_ = v___y_3195_;
                    v___y_3151_ = v___y_3196_;
                    v___y_3152_ = v___y_3197_;
                    v___y_3153_ = v___y_3198_;
                    v___y_3154_ = v___y_3199_;
                    v___y_3155_ = v___y_3200_;
                    v___y_3156_ = v___x_3204_;
                    v___y_3157_ = v___y_3201_;
                    v___y_3158_ = v___x_3216_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v___x_3238_ = l_Lean_Elab_Command_elabBinderPred___closed__43;
                v___x_3239_ = l_Lean_Elab_Command_elabBinderPred___closed__44;
                v___x_3240_ = l_Lean_Elab_Command_elabBinderPred___closed__46;
                v___x_3241_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabBinderPred___closed__47),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabBinderPred___closed__47_once),
                    _init_l_Lean_Elab_Command_elabBinderPred___closed__47,
                );
                if lean_obj_tag(v___y_3236_) == 1 {
                    v_val_3242_ = lean_ctor_get(v___y_3236_, 0);
                    lean_inc(v_val_3242_);
                    v___x_3243_ = l_Array_mkArray1___redArg(v_val_3242_);
                    v___y_3178_ = v___y_3218_;
                    v___y_3179_ = v___y_3219_;
                    v___y_3180_ = v___y_3220_;
                    v___y_3181_ = v___y_3222_;
                    v___y_3182_ = v___y_3223_;
                    v___y_3183_ = v___x_3239_;
                    v___y_3184_ = v___y_3225_;
                    v___y_3185_ = v___x_3238_;
                    v___y_3186_ = v___y_3226_;
                    v___y_3187_ = v___x_3241_;
                    v___y_3188_ = v___y_3231_;
                    v___y_3189_ = v_a_3237_;
                    v___y_3190_ = v___y_3233_;
                    v___y_3191_ = v___x_3240_;
                    v___y_3192_ = v___y_3234_;
                    v___y_3193_ = v___y_3235_;
                    v___y_3194_ = v___y_3236_;
                    v___y_3195_ = v___y_3221_;
                    v___y_3196_ = v___y_3224_;
                    v___y_3197_ = v___y_3228_;
                    v___y_3198_ = v___y_3227_;
                    v___y_3199_ = v___y_3229_;
                    v___y_3200_ = v___y_3230_;
                    v___y_3201_ = v___y_3232_;
                    v___y_3202_ = v___x_3243_;
                    state = 11;
                    continue;
                } else {
                    v___x_3244_ = l_Lean_Elab_Command_elabBinderPred___closed__23;
                    v___y_3178_ = v___y_3218_;
                    v___y_3179_ = v___y_3219_;
                    v___y_3180_ = v___y_3220_;
                    v___y_3181_ = v___y_3222_;
                    v___y_3182_ = v___y_3223_;
                    v___y_3183_ = v___x_3239_;
                    v___y_3184_ = v___y_3225_;
                    v___y_3185_ = v___x_3238_;
                    v___y_3186_ = v___y_3226_;
                    v___y_3187_ = v___x_3241_;
                    v___y_3188_ = v___y_3231_;
                    v___y_3189_ = v_a_3237_;
                    v___y_3190_ = v___y_3233_;
                    v___y_3191_ = v___x_3240_;
                    v___y_3192_ = v___y_3234_;
                    v___y_3193_ = v___y_3235_;
                    v___y_3194_ = v___y_3236_;
                    v___y_3195_ = v___y_3221_;
                    v___y_3196_ = v___y_3224_;
                    v___y_3197_ = v___y_3228_;
                    v___y_3198_ = v___y_3227_;
                    v___y_3199_ = v___y_3229_;
                    v___y_3200_ = v___y_3230_;
                    v___y_3201_ = v___y_3232_;
                    v___y_3202_ = v___x_3244_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_3256_ =
                    lean_alloc_closure(l_Lean_evalOptPrio___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___x_3256_, 0, v_prio_x3f_3253_);
                v___x_3257_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg(v___x_3256_, v___y_3254_, v___y_3255_);
                if lean_obj_tag(v___x_3257_) == 0 {
                    v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
                    lean_inc(v_a_3258_);
                    lean_dec_ref_known(v___x_3257_, 1);
                    v___x_3259_ = lean_unsigned_to_nat(7);
                    v___x_3260_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3259_);
                    v_args_3261_ = l_Lean_Syntax_getArgs(v___x_3260_);
                    lean_dec(v___x_3260_);
                    v_sz_3262_ = lean_array_size(v_args_3261_);
                    v___x_3263_ = 0usize;
                    v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabBinderPred_spec__2(v_sz_3262_, v___x_3263_, v_args_3261_, v___y_3254_, v___y_3255_);
                    if lean_obj_tag(v___x_3264_) == 0 {
                        v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
                        lean_inc(v_a_3265_);
                        lean_dec_ref_known(v___x_3264_, 1);
                        v___x_3266_ = l_Array_unzip___redArg(v_a_3265_);
                        lean_dec(v_a_3265_);
                        v_fst_3267_ = lean_ctor_get(v___x_3266_, 0);
                        lean_inc(v_fst_3267_);
                        v_snd_3268_ = lean_ctor_get(v___x_3266_, 1);
                        lean_inc(v_snd_3268_);
                        lean_dec_ref(v___x_3266_);
                        v___x_3269_ = l_Lean_Elab_Command_getRef___redArg(v___y_3254_);
                        if lean_obj_tag(v___x_3269_) == 0 {
                            v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
                            lean_inc(v_a_3270_);
                            lean_dec_ref_known(v___x_3269_, 1);
                            v___x_3271_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3254_);
                            if lean_obj_tag(v___x_3271_) == 0 {
                                v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
                                lean_inc(v_a_3272_);
                                lean_dec_ref_known(v___x_3271_, 1);
                                v_quotContext_x3f_3273_ = lean_ctor_get(v___y_3254_, 5);
                                v___x_3274_ = l_Lean_Elab_Command_elabBinderPred___closed__48;
                                v___x_3275_ = lean_unsigned_to_nat(6);
                                v___x_3276_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3275_);
                                v___x_3277_ = lean_unsigned_to_nat(9);
                                v___x_3278_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3277_);
                                lean_dec(v_stx_2939_);
                                v___x_3279_ = 0;
                                v___x_3280_ = l_Lean_SourceInfo_fromRef(v_a_3270_, v___x_3279_);
                                lean_dec(v_a_3270_);
                                if lean_obj_tag(v_quotContext_x3f_3273_) == 0 {
                                    v___x_3281_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabBinderPred_spec__4___redArg(v___y_3255_);
                                    v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
                                    lean_inc(v_a_3282_);
                                    lean_dec_ref(v___x_3281_);
                                    v___y_3218_ = v_a_3258_;
                                    v___y_3219_ = v___x_3279_;
                                    v___y_3220_ = v___y_3246_;
                                    v___y_3221_ = v_snd_3268_;
                                    v___y_3222_ = v___y_3247_;
                                    v___y_3223_ = v_a_3272_;
                                    v___y_3224_ = v___y_3255_;
                                    v___y_3225_ = v___x_3278_;
                                    v___y_3226_ = v___y_3249_;
                                    v___y_3227_ = v___x_3274_;
                                    v___y_3228_ = v_fst_3267_;
                                    v___y_3229_ = v___x_3263_;
                                    v___y_3230_ = v___y_3254_;
                                    v___y_3231_ = v___x_3280_;
                                    v___y_3232_ = v___y_3248_;
                                    v___y_3233_ = v___y_3250_;
                                    v___y_3234_ = v___y_3251_;
                                    v___y_3235_ = v___x_3276_;
                                    v___y_3236_ = v___y_3252_;
                                    v_a_3237_ = v_a_3282_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_val_3283_ = lean_ctor_get(v_quotContext_x3f_3273_, 0);
                                    lean_inc(v_val_3283_);
                                    v___y_3218_ = v_a_3258_;
                                    v___y_3219_ = v___x_3279_;
                                    v___y_3220_ = v___y_3246_;
                                    v___y_3221_ = v_snd_3268_;
                                    v___y_3222_ = v___y_3247_;
                                    v___y_3223_ = v_a_3272_;
                                    v___y_3224_ = v___y_3255_;
                                    v___y_3225_ = v___x_3278_;
                                    v___y_3226_ = v___y_3249_;
                                    v___y_3227_ = v___x_3274_;
                                    v___y_3228_ = v_fst_3267_;
                                    v___y_3229_ = v___x_3263_;
                                    v___y_3230_ = v___y_3254_;
                                    v___y_3231_ = v___x_3280_;
                                    v___y_3232_ = v___y_3248_;
                                    v___y_3233_ = v___y_3250_;
                                    v___y_3234_ = v___y_3251_;
                                    v___y_3235_ = v___x_3276_;
                                    v___y_3236_ = v___y_3252_;
                                    v_a_3237_ = v_val_3283_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3270_);
                                lean_dec(v_snd_3268_);
                                lean_dec(v_fst_3267_);
                                lean_dec(v_a_3258_);
                                lean_dec(v___y_3252_);
                                lean_dec(v___y_3249_);
                                lean_dec(v___y_3248_);
                                lean_dec(v___y_3247_);
                                lean_dec(v___y_3246_);
                                lean_dec(v_stx_2939_);
                                v_a_3284_ = lean_ctor_get(v___x_3271_, 0);
                                v_isSharedCheck_3291_ = (!lean_is_exclusive(v___x_3271_)) as u8;
                                if v_isSharedCheck_3291_ == 0 {
                                    v___x_3286_ = v___x_3271_;
                                    v_isShared_3287_ = v_isSharedCheck_3291_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_3284_);
                                    lean_dec(v___x_3271_);
                                    v___x_3286_ = lean_box(0);
                                    v_isShared_3287_ = v_isSharedCheck_3291_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_snd_3268_);
                            lean_dec(v_fst_3267_);
                            lean_dec(v_a_3258_);
                            lean_dec(v___y_3252_);
                            lean_dec(v___y_3249_);
                            lean_dec(v___y_3248_);
                            lean_dec(v___y_3247_);
                            lean_dec(v___y_3246_);
                            lean_dec(v_stx_2939_);
                            v_a_3292_ = lean_ctor_get(v___x_3269_, 0);
                            v_isSharedCheck_3299_ = (!lean_is_exclusive(v___x_3269_)) as u8;
                            if v_isSharedCheck_3299_ == 0 {
                                v___x_3294_ = v___x_3269_;
                                v_isShared_3295_ = v_isSharedCheck_3299_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_3292_);
                                lean_dec(v___x_3269_);
                                v___x_3294_ = lean_box(0);
                                v_isShared_3295_ = v_isSharedCheck_3299_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3258_);
                        lean_dec(v___y_3252_);
                        lean_dec(v___y_3249_);
                        lean_dec(v___y_3248_);
                        lean_dec(v___y_3247_);
                        lean_dec(v___y_3246_);
                        lean_dec(v_stx_2939_);
                        v_a_3300_ = lean_ctor_get(v___x_3264_, 0);
                        v_isSharedCheck_3307_ = (!lean_is_exclusive(v___x_3264_)) as u8;
                        if v_isSharedCheck_3307_ == 0 {
                            v___x_3302_ = v___x_3264_;
                            v_isShared_3303_ = v_isSharedCheck_3307_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_3300_);
                            lean_dec(v___x_3264_);
                            v___x_3302_ = lean_box(0);
                            v_isShared_3303_ = v_isSharedCheck_3307_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3252_);
                    lean_dec(v___y_3249_);
                    lean_dec(v___y_3248_);
                    lean_dec(v___y_3247_);
                    lean_dec(v___y_3246_);
                    lean_dec(v_stx_2939_);
                    v_a_3308_ = lean_ctor_get(v___x_3257_, 0);
                    v_isSharedCheck_3315_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                    if v_isSharedCheck_3315_ == 0 {
                        v___x_3310_ = v___x_3257_;
                        v_isShared_3311_ = v_isSharedCheck_3315_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_3308_);
                        lean_dec(v___x_3257_);
                        v___x_3310_ = lean_box(0);
                        v_isShared_3311_ = v_isSharedCheck_3315_;
                        state = 20;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3287_ == 0 {
                    v___x_3289_ = v___x_3286_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3289_;
            }
            16 => {
                if v_isShared_3295_ == 0 {
                    v___x_3297_ = v___x_3294_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
                    v___x_3297_ = v_reuseFailAlloc_3298_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3297_;
            }
            18 => {
                if v_isShared_3303_ == 0 {
                    v___x_3305_ = v___x_3302_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
                    v___x_3305_ = v_reuseFailAlloc_3306_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3305_;
            }
            20 => {
                if v_isShared_3311_ == 0 {
                    v___x_3313_ = v___x_3310_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
                    v___x_3313_ = v_reuseFailAlloc_3314_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3313_;
            }
            22 => {
                v___x_3328_ = lean_unsigned_to_nat(5);
                v___x_3329_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3328_);
                v___x_3330_ = l_Lean_Syntax_isNone(v___x_3329_);
                if v___x_3330_ == 0 {
                    lean_inc(v___x_3329_);
                    v___x_3331_ = l_Lean_Syntax_matchesNull(v___x_3329_, v___y_3323_);
                    if v___x_3331_ == 0 {
                        lean_dec(v___x_3329_);
                        lean_dec(v_name_x3f_3325_);
                        lean_dec(v___y_3324_);
                        lean_dec(v___y_3320_);
                        lean_dec(v___y_3319_);
                        lean_dec(v___y_3318_);
                        lean_dec(v_stx_2939_);
                        v___x_3332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                        return v___x_3332_;
                    } else {
                        v___x_3333_ = l_Lean_Syntax_getArg(v___x_3329_, v___x_3010_);
                        lean_dec(v___x_3329_);
                        v___x_3334_ = l_Lean_Elab_Command_elabBinderPred___closed__25;
                        lean_inc(v___x_3333_);
                        v___x_3335_ = l_Lean_Syntax_isOfKind(v___x_3333_, v___x_3334_);
                        if v___x_3335_ == 0 {
                            lean_dec(v___x_3333_);
                            lean_dec(v_name_x3f_3325_);
                            lean_dec(v___y_3324_);
                            lean_dec(v___y_3320_);
                            lean_dec(v___y_3319_);
                            lean_dec(v___y_3318_);
                            lean_dec(v_stx_2939_);
                            v___x_3336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                            return v___x_3336_;
                        } else {
                            v_prio_x3f_3337_ = l_Lean_Syntax_getArg(v___x_3333_, v___y_3317_);
                            lean_dec(v___x_3333_);
                            v___x_3338_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3338_, 0, v_prio_x3f_3337_);
                            v___y_3246_ = v___y_3318_;
                            v___y_3247_ = v___y_3319_;
                            v___y_3248_ = v_name_x3f_3325_;
                            v___y_3249_ = v___y_3320_;
                            v___y_3250_ = v___y_3321_;
                            v___y_3251_ = v___y_3322_;
                            v___y_3252_ = v___y_3324_;
                            v_prio_x3f_3253_ = v___x_3338_;
                            v___y_3254_ = v___y_3326_;
                            v___y_3255_ = v___y_3327_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3329_);
                    v___x_3339_ = lean_box(0);
                    v___y_3246_ = v___y_3318_;
                    v___y_3247_ = v___y_3319_;
                    v___y_3248_ = v_name_x3f_3325_;
                    v___y_3249_ = v___y_3320_;
                    v___y_3250_ = v___y_3321_;
                    v___y_3251_ = v___y_3322_;
                    v___y_3252_ = v___y_3324_;
                    v_prio_x3f_3253_ = v___x_3339_;
                    v___y_3254_ = v___y_3326_;
                    v___y_3255_ = v___y_3327_;
                    state = 13;
                    continue;
                }
            }
            23 => {
                v___x_3346_ = lean_unsigned_to_nat(2);
                v___x_3347_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3346_);
                lean_inc(v___x_3347_);
                v___x_3348_ = l_Lean_Syntax_matchesNull(v___x_3347_, v___y_3341_);
                if v___x_3348_ == 0 {
                    lean_dec(v___x_3347_);
                    lean_dec(v_attrs_x3f_3343_);
                    lean_dec(v___y_3342_);
                    lean_dec(v_stx_2939_);
                    v___x_3349_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                    return v___x_3349_;
                } else {
                    v___x_3350_ = l_Lean_Syntax_getArg(v___x_3347_, v___x_3010_);
                    lean_dec(v___x_3347_);
                    v___x_3351_ = l_Lean_Elab_Command_elabBinderPred___closed__49;
                    v___x_3352_ = l_Lean_Elab_Command_elabBinderPred___closed__51;
                    lean_inc(v___x_3350_);
                    v___x_3353_ = l_Lean_Syntax_isOfKind(v___x_3350_, v___x_3352_);
                    if v___x_3353_ == 0 {
                        lean_dec(v___x_3350_);
                        lean_dec(v_attrs_x3f_3343_);
                        lean_dec(v___y_3342_);
                        lean_dec(v_stx_2939_);
                        v___x_3354_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                        return v___x_3354_;
                    } else {
                        v___x_3355_ = lean_unsigned_to_nat(3);
                        v_tk_3356_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3355_);
                        v___x_3357_ = lean_unsigned_to_nat(4);
                        v___x_3358_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3357_);
                        v___x_3359_ = l_Lean_Syntax_isNone(v___x_3358_);
                        if v___x_3359_ == 0 {
                            lean_inc(v___x_3358_);
                            v___x_3360_ = l_Lean_Syntax_matchesNull(v___x_3358_, v___y_3341_);
                            if v___x_3360_ == 0 {
                                lean_dec(v___x_3358_);
                                lean_dec(v_tk_3356_);
                                lean_dec(v___x_3350_);
                                lean_dec(v_attrs_x3f_3343_);
                                lean_dec(v___y_3342_);
                                lean_dec(v_stx_2939_);
                                v___x_3361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                                return v___x_3361_;
                            } else {
                                v___x_3362_ = l_Lean_Syntax_getArg(v___x_3358_, v___x_3010_);
                                lean_dec(v___x_3358_);
                                v___x_3363_ = l_Lean_Elab_Command_elabBinderPred___closed__38;
                                lean_inc(v___x_3362_);
                                v___x_3364_ = l_Lean_Syntax_isOfKind(v___x_3362_, v___x_3363_);
                                if v___x_3364_ == 0 {
                                    lean_dec(v___x_3362_);
                                    lean_dec(v_tk_3356_);
                                    lean_dec(v___x_3350_);
                                    lean_dec(v_attrs_x3f_3343_);
                                    lean_dec(v___y_3342_);
                                    lean_dec(v_stx_2939_);
                                    v___x_3365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                                    return v___x_3365_;
                                } else {
                                    v_name_x3f_3366_ =
                                        l_Lean_Syntax_getArg(v___x_3362_, v___x_3355_);
                                    lean_dec(v___x_3362_);
                                    v___x_3367_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_3367_, 0, v_name_x3f_3366_);
                                    v___y_3317_ = v___x_3355_;
                                    v___y_3318_ = v_attrs_x3f_3343_;
                                    v___y_3319_ = v_tk_3356_;
                                    v___y_3320_ = v___x_3350_;
                                    v___y_3321_ = v___x_3351_;
                                    v___y_3322_ = v___x_3352_;
                                    v___y_3323_ = v___y_3341_;
                                    v___y_3324_ = v___y_3342_;
                                    v_name_x3f_3325_ = v___x_3367_;
                                    v___y_3326_ = v___y_3344_;
                                    v___y_3327_ = v___y_3345_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_3358_);
                            v___x_3368_ = lean_box(0);
                            v___y_3317_ = v___x_3355_;
                            v___y_3318_ = v_attrs_x3f_3343_;
                            v___y_3319_ = v_tk_3356_;
                            v___y_3320_ = v___x_3350_;
                            v___y_3321_ = v___x_3351_;
                            v___y_3322_ = v___x_3352_;
                            v___y_3323_ = v___y_3341_;
                            v___y_3324_ = v___y_3342_;
                            v_name_x3f_3325_ = v___x_3368_;
                            v___y_3326_ = v___y_3344_;
                            v___y_3327_ = v___y_3345_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            24 => {
                v___x_3373_ = lean_unsigned_to_nat(1);
                v___x_3374_ = l_Lean_Syntax_getArg(v_stx_2939_, v___x_3373_);
                v___x_3375_ = l_Lean_Syntax_isNone(v___x_3374_);
                if v___x_3375_ == 0 {
                    lean_inc(v___x_3374_);
                    v___x_3376_ = l_Lean_Syntax_matchesNull(v___x_3374_, v___x_3373_);
                    if v___x_3376_ == 0 {
                        lean_dec(v___x_3374_);
                        lean_dec(v_doc_x3f_3370_);
                        lean_dec(v_stx_2939_);
                        v___x_3377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                        return v___x_3377_;
                    } else {
                        v___x_3378_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3010_);
                        lean_dec(v___x_3374_);
                        v___x_3379_ = l_Lean_Elab_Command_elabBinderPred___closed__52;
                        lean_inc(v___x_3378_);
                        v___x_3380_ = l_Lean_Syntax_isOfKind(v___x_3378_, v___x_3379_);
                        if v___x_3380_ == 0 {
                            lean_dec(v___x_3378_);
                            lean_dec(v_doc_x3f_3370_);
                            lean_dec(v_stx_2939_);
                            v___x_3381_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabBinderPred_spec__0___redArg();
                            return v___x_3381_;
                        } else {
                            v___x_3382_ = l_Lean_Syntax_getArg(v___x_3378_, v___x_3373_);
                            lean_dec(v___x_3378_);
                            v_attrs_x3f_3383_ = l_Lean_Syntax_getArgs(v___x_3382_);
                            lean_dec(v___x_3382_);
                            v___x_3384_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3384_, 0, v_attrs_x3f_3383_);
                            v___y_3341_ = v___x_3373_;
                            v___y_3342_ = v_doc_x3f_3370_;
                            v_attrs_x3f_3343_ = v___x_3384_;
                            v___y_3344_ = v___y_3371_;
                            v___y_3345_ = v___y_3372_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3374_);
                    v___x_3385_ = lean_box(0);
                    v___y_3341_ = v___x_3373_;
                    v___y_3342_ = v_doc_x3f_3370_;
                    v_attrs_x3f_3343_ = v___x_3385_;
                    v___y_3344_ = v___y_3371_;
                    v___y_3345_ = v___y_3372_;
                    state = 23;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabBinderPred___boxed(
    mut v_stx_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
    mut v_a_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3401_: *mut LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_Elab_Command_elabBinderPred(v_stx_3397_, v_a_3398_, v_a_3399_);
    lean_dec(v_a_3399_);
    lean_dec_ref(v_a_3398_);
    return v_res_3401_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2(
    mut v_00_u03b1_3402_: *mut LeanObject,
    mut v_x_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    v___x_3406_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2___redArg(v_x_3403_, v___y_3405_);
    return v___x_3406_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2___boxed(
    mut v_00_u03b1_3407_: *mut LeanObject,
    mut v_x_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3411_: *mut LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__2(v_00_u03b1_3407_, v_x_3408_, v___y_3409_, v___y_3410_);
    lean_dec_ref(v___y_3409_);
    lean_dec_ref(v_x_3408_);
    return v_res_3411_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7(
    mut v_00_u03b1_3412_: *mut LeanObject,
    mut v_ref_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3417_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___redArg(v_ref_3413_);
    return v___x_3417_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7___boxed(
    mut v_00_u03b1_3418_: *mut LeanObject,
    mut v_ref_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3423_: *mut LeanObject = core::ptr::null_mut();
    v_res_3423_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__7(v_00_u03b1_3418_, v_ref_3419_, v___y_3420_, v___y_3421_);
    lean_dec(v___y_3421_);
    lean_dec_ref(v___y_3420_);
    return v_res_3423_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1(
    mut v_00_u03b1_3424_: *mut LeanObject,
    mut v_x_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
    mut v___y_3427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    v___x_3429_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___redArg(
        v_x_3425_,
        v___y_3426_,
        v___y_3427_,
    );
    return v___x_3429_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1___boxed(
    mut v_00_u03b1_3430_: *mut LeanObject,
    mut v_x_3431_: *mut LeanObject,
    mut v___y_3432_: *mut LeanObject,
    mut v___y_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3435_: *mut LeanObject = core::ptr::null_mut();
    v_res_3435_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1(
        v_00_u03b1_3430_,
        v_x_3431_,
        v___y_3432_,
        v___y_3433_,
    );
    lean_dec(v___y_3433_);
    lean_dec_ref(v___y_3432_);
    return v_res_3435_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3(
    mut v_msgData_3436_: *mut LeanObject,
    mut v___y_3437_: *mut LeanObject,
    mut v___y_3438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3440_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___redArg(v_msgData_3436_, v___y_3438_);
    return v___x_3440_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_3441_: *mut LeanObject,
    mut v___y_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3445_: *mut LeanObject = core::ptr::null_mut();
    v_res_3445_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__1_spec__3(v_msgData_3441_, v___y_3442_, v___y_3443_);
    lean_dec(v___y_3443_);
    lean_dec_ref(v___y_3442_);
    return v_res_3445_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4(
    mut v_as_3446_: *mut LeanObject,
    mut v_as_x27_3447_: *mut LeanObject,
    mut v_b_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    v___x_3453_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4___redArg(v_as_x27_3447_, v_b_3448_, v___y_3450_, v___y_3451_);
    return v___x_3453_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4___boxed(
    mut v_as_3454_: *mut LeanObject,
    mut v_as_x27_3455_: *mut LeanObject,
    mut v_b_3456_: *mut LeanObject,
    mut v_a_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3461_: *mut LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__4(v_as_3454_, v_as_x27_3455_, v_b_3456_, v_a_3457_, v___y_3458_, v___y_3459_);
    lean_dec(v___y_3459_);
    lean_dec_ref(v___y_3458_);
    lean_dec(v_as_x27_3455_);
    lean_dec(v_as_3454_);
    return v_res_3461_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6(
    mut v_00_u03b1_3462_: *mut LeanObject,
    mut v_ref_3463_: *mut LeanObject,
    mut v_msg_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
    mut v___y_3466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6___redArg(v_ref_3463_, v_msg_3464_, v___y_3465_, v___y_3466_);
    return v___x_3468_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6___boxed(
    mut v_00_u03b1_3469_: *mut LeanObject,
    mut v_ref_3470_: *mut LeanObject,
    mut v_msg_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3475_: *mut LeanObject = core::ptr::null_mut();
    v_res_3475_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6(v_00_u03b1_3469_, v_ref_3470_, v_msg_3471_, v___y_3472_, v___y_3473_);
    lean_dec(v___y_3473_);
    lean_dec_ref(v___y_3472_);
    lean_dec(v_ref_3470_);
    return v_res_3475_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8(
    mut v_00_u03b2_3476_: *mut LeanObject,
    mut v_m_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    v___x_3479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___redArg(v_m_3477_, v_a_3478_);
    return v___x_3479_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_3480_: *mut LeanObject,
    mut v_m_3481_: *mut LeanObject,
    mut v_a_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3483_: *mut LeanObject = core::ptr::null_mut();
    v_res_3483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8(v_00_u03b2_3480_, v_m_3481_, v_a_3482_);
    lean_dec(v_a_3482_);
    lean_dec_ref(v_m_3481_);
    return v_res_3483_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12(
    mut v_00_u03b1_3484_: *mut LeanObject,
    mut v_msg_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    v___x_3489_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12___redArg(v_msg_3485_, v___y_3486_, v___y_3487_);
    return v___x_3489_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12___boxed(
    mut v_00_u03b1_3490_: *mut LeanObject,
    mut v_msg_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3495_: *mut LeanObject = core::ptr::null_mut();
    v_res_3495_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12(v_00_u03b1_3490_, v_msg_3491_, v___y_3492_, v___y_3493_);
    lean_dec(v___y_3493_);
    lean_dec_ref(v___y_3492_);
    return v_res_3495_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10(
    mut v_00_u03b2_3496_: *mut LeanObject,
    mut v_x_3497_: *mut LeanObject,
    mut v_x_3498_: *mut LeanObject,
) -> u8 {
    let mut v___x_3499_: u8 = 0;
    v___x_3499_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10___redArg(v_x_3497_, v_x_3498_);
    return v___x_3499_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10___boxed(
    mut v_00_u03b2_3500_: *mut LeanObject,
    mut v_x_3501_: *mut LeanObject,
    mut v_x_3502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3503_: u8 = 0;
    let mut v_r_3504_: *mut LeanObject = core::ptr::null_mut();
    v_res_3503_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_3500_, v_x_3501_, v_x_3502_);
    lean_dec_ref(v_x_3502_);
    lean_dec_ref(v_x_3501_);
    v_r_3504_ = lean_box((v_res_3503_) as usize);
    return v_r_3504_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13(
    mut v_00_u03b2_3505_: *mut LeanObject,
    mut v_a_3506_: *mut LeanObject,
    mut v_x_3507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v___x_3508_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13___redArg(v_a_3506_, v_x_3507_);
    return v___x_3508_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13___boxed(
    mut v_00_u03b2_3509_: *mut LeanObject,
    mut v_a_3510_: *mut LeanObject,
    mut v_x_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3512_: *mut LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__8_spec__13(v_00_u03b2_3509_, v_a_3510_, v_x_3511_);
    lean_dec(v_x_3511_);
    lean_dec(v_a_3510_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18(
    mut v_msgData_3513_: *mut LeanObject,
    mut v_macroStack_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
    mut v___y_3516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    v___x_3518_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___redArg(v_msgData_3513_, v_macroStack_3514_, v___y_3516_);
    return v___x_3518_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18___boxed(
    mut v_msgData_3519_: *mut LeanObject,
    mut v_macroStack_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3524_: *mut LeanObject = core::ptr::null_mut();
    v_res_3524_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__6_spec__12_spec__18(v_msgData_3519_, v_macroStack_3520_, v___y_3521_, v___y_3522_);
    lean_dec(v___y_3522_);
    lean_dec_ref(v___y_3521_);
    return v_res_3524_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14(
    mut v_00_u03b2_3525_: *mut LeanObject,
    mut v_x_3526_: *mut LeanObject,
    mut v_x_3527_: usize,
    mut v_x_3528_: *mut LeanObject,
) -> u8 {
    let mut v___x_3529_: u8 = 0;
    v___x_3529_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(v_x_3526_, v_x_3527_, v_x_3528_);
    return v___x_3529_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14___boxed(
    mut v_00_u03b2_3530_: *mut LeanObject,
    mut v_x_3531_: *mut LeanObject,
    mut v_x_3532_: *mut LeanObject,
    mut v_x_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_23736__boxed_3534_: usize = 0;
    let mut v_res_3535_: u8 = 0;
    let mut v_r_3536_: *mut LeanObject = core::ptr::null_mut();
    v_x_23736__boxed_3534_ = lean_unbox_usize(v_x_3532_);
    lean_dec(v_x_3532_);
    v_res_3535_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14(v_00_u03b2_3530_, v_x_3531_, v_x_23736__boxed_3534_, v_x_3533_);
    lean_dec_ref(v_x_3533_);
    lean_dec_ref(v_x_3531_);
    v_r_3536_ = lean_box((v_res_3535_) as usize);
    return v_r_3536_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18(
    mut v_00_u03b2_3537_: *mut LeanObject,
    mut v_keys_3538_: *mut LeanObject,
    mut v_vals_3539_: *mut LeanObject,
    mut v_heq_3540_: *mut LeanObject,
    mut v_i_3541_: *mut LeanObject,
    mut v_k_3542_: *mut LeanObject,
) -> u8 {
    let mut v___x_3543_: u8 = 0;
    v___x_3543_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(v_keys_3538_, v_i_3541_, v_k_3542_);
    return v___x_3543_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___boxed(
    mut v_00_u03b2_3544_: *mut LeanObject,
    mut v_keys_3545_: *mut LeanObject,
    mut v_vals_3546_: *mut LeanObject,
    mut v_heq_3547_: *mut LeanObject,
    mut v_i_3548_: *mut LeanObject,
    mut v_k_3549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3550_: u8 = 0;
    let mut v_r_3551_: *mut LeanObject = core::ptr::null_mut();
    v_res_3550_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabBinderPred_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18(v_00_u03b2_3544_, v_keys_3545_, v_vals_3546_, v_heq_3547_, v_i_3548_, v_k_3549_);
    lean_dec_ref(v_k_3549_);
    lean_dec_ref(v_vals_3546_);
    lean_dec_ref(v_keys_3545_);
    v_r_3551_ = lean_box((v_res_3550_) as usize);
    return v_r_3551_;
}
pub unsafe fn l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1()
-> *mut LeanObject {
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    v___x_3560_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3561_ = l_Lean_Elab_Command_elabBinderPred___closed__20;
    v___x_3562_ = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2;
    v___x_3563_ = lean_alloc_closure(
        l_Lean_Elab_Command_elabBinderPred___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3564_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3560_,
        v___x_3561_,
        v___x_3562_,
        v___x_3563_,
    );
    return v___x_3564_;
}
pub unsafe fn l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___boxed(
    mut v_a_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3566_: *mut LeanObject = core::ptr::null_mut();
    v_res_3566_ = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1();
    return v_res_3566_;
}
pub unsafe fn l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3()
-> *mut LeanObject {
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    v___x_3593_ = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1___closed__2;
    v___x_3594_ = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___closed__6;
    v___x_3595_ = l_Lean_addBuiltinDeclarationRanges(v___x_3593_, v___x_3594_);
    return v___x_3595_;
}
pub unsafe fn l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3___boxed(
    mut v_a_3596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3597_: *mut LeanObject = core::ptr::null_mut();
    v_res_3597_ = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3();
    return v_res_3597_;
}
pub unsafe fn l_Lean_Elab_Command_checkBinderPredicate(
    mut v_stx_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3614_: u8 = 0;
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: u8 = 0;
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: u8 = 0;
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3612_ = lean_unsigned_to_nat(0);
                v___x_3627_ = l_Lean_Syntax_getArg(v_stx_3605_, v___x_3612_);
                v___x_3628_ = l_Lean_Syntax_isNone(v___x_3627_);
                lean_dec(v___x_3627_);
                if v___x_3628_ == 0 {
                    v___y_3614_ = v___x_3628_;
                    state = 2;
                    continue;
                } else {
                    v___x_3629_ = lean_unsigned_to_nat(2);
                    v___x_3630_ = l_Lean_Syntax_getArg(v_stx_3605_, v___x_3629_);
                    v___x_3631_ = l_Lean_Syntax_getArg(v___x_3630_, v___x_3612_);
                    lean_dec(v___x_3630_);
                    v___x_3632_ = l_Lean_Syntax_getArg(v___x_3631_, v___x_3612_);
                    lean_dec(v___x_3631_);
                    v___x_3633_ = l_Lean_Syntax_getKind(v___x_3632_);
                    v___x_3634_ = l_Lean_Elab_Command_checkBinderPredicate___closed__2;
                    v___x_3635_ = lean_name_eq(v___x_3633_, v___x_3634_);
                    lean_dec(v___x_3633_);
                    if v___x_3635_ == 0 {
                        v___y_3614_ = v___x_3628_;
                        state = 2;
                        continue;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3610_ = lean_box(0);
                v___x_3611_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3611_, 0, v___x_3610_);
                return v___x_3611_;
            }
            2 => {
                if v___y_3614_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3615_ = lean_unsigned_to_nat(4);
                    v___x_3616_ = l_Lean_Syntax_getArg(v_stx_3605_, v___x_3615_);
                    v___x_3617_ = l_Lean_Syntax_isNone(v___x_3616_);
                    if v___x_3617_ == 0 {
                        v___x_3618_ = l_Lean_Syntax_getArg(v___x_3616_, v___x_3612_);
                        lean_dec(v___x_3616_);
                        v___x_3619_ = lean_unsigned_to_nat(3);
                        v___x_3620_ = l_Lean_Syntax_getArg(v___x_3618_, v___x_3619_);
                        lean_dec(v___x_3618_);
                        v___x_3621_ = l_Lean_Elab_Command_checkBinderPredicate___closed__0;
                        v___x_3622_ = l_Lean_Linter_MissingDocs_lintNamed(
                            v___x_3620_,
                            v___x_3621_,
                            v_a_3606_,
                            v_a_3607_,
                        );
                        lean_dec(v___x_3620_);
                        return v___x_3622_;
                    } else {
                        lean_dec(v___x_3616_);
                        v___x_3623_ = lean_unsigned_to_nat(3);
                        v___x_3624_ = l_Lean_Syntax_getArg(v_stx_3605_, v___x_3623_);
                        v___x_3625_ = l_Lean_Elab_Command_checkBinderPredicate___closed__0;
                        v___x_3626_ = l_Lean_Linter_MissingDocs_lint(
                            v___x_3624_,
                            v___x_3625_,
                            v_a_3606_,
                            v_a_3607_,
                        );
                        lean_dec(v___x_3624_);
                        return v___x_3626_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_checkBinderPredicate___boxed(
    mut v_stx_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
    mut v_a_3638_: *mut LeanObject,
    mut v_a_3639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3640_: *mut LeanObject = core::ptr::null_mut();
    v_res_3640_ = l_Lean_Elab_Command_checkBinderPredicate(v_stx_3636_, v_a_3637_, v_a_3638_);
    lean_dec(v_a_3638_);
    lean_dec_ref(v_a_3637_);
    lean_dec(v_stx_3636_);
    return v_res_3640_;
}
pub unsafe fn _init_l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    v___x_3641_ = lean_alloc_closure(
        l_Lean_Elab_Command_checkBinderPredicate___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3642_ = lean_alloc_closure(
        l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_3642_, 0, v___x_3641_);
    return v___x_3642_;
}
pub unsafe fn l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1()
-> *mut LeanObject {
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    v___x_3644_ = l_Lean_Elab_Command_elabBinderPred___closed__20;
    v___x_3645_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1___closed__0_once), _init_l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1___closed__0);
    v___x_3646_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3644_, v___x_3645_);
    return v___x_3646_;
}
pub unsafe fn l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1___boxed(
    mut v_a_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3648_: *mut LeanObject = core::ptr::null_mut();
    v_res_3648_ = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1();
    return v_res_3648_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BinderPredicates(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_MacroArgUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_MissingDocs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_elabBinderPred___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_BinderPredicates_0__Lean_Elab_Command_checkBinderPredicate___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BinderPredicates(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BinderPredicates(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_MacroArgUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_MissingDocs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_BinderPredicates(builtin);
}
