// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Driver
// Imports: Lean.Elab.Tactic.Meta Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.Solve Lean.Meta.Sym.Grind
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Tactic::Do::Attr::l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType;
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Context::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Solve::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solve,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Util::{
    l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl,
};
use crate::r#gen::Lean::Elab::Tactic::Meta::{
    initialize_Lean_Elab_Tactic_Meta, l_Lean_Elab_runTactic,
    runtime_initialize_Lean_Elab_Tactic_Meta,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_setKind___redArg,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64,
};
use crate::r#gen::Lean::Meta::Sym::Grind::{
    initialize_Lean_Meta_Sym_Grind, l_Lean_Meta_Grind_Goal_grind,
    runtime_initialize_Lean_Meta_Sym_Grind,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Sym::Util::{
    l_Lean_Meta_Sym_preprocessMVar, l_Lean_Meta_Sym_unfoldReducible,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::l_Lean_Meta_Grind_mkGoalCore;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_MVarId_setTag___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_MetavarContext_getExprAssignmentCore_x3f;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 102, 97, 105, 108, 101, 100, 32, 111, 110, 32, 103,
        111, 97, 108, 58, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4_value:
    crate::leanh::LeanCtorObject<10> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
            + 16) as u16,
        other: 8,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16843009 as *mut crate::leanh::LeanObject,
        65537 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5_value:
    crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2: u64 = 0;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        105, 110, 118, 97, 114, 105, 97, 110, 116, 68, 111, 116, 65, 108, 116, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4649390856739084974 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        105, 110, 118, 97, 114, 105, 97, 110, 116, 67, 97, 115, 101, 65, 108, 116, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value)
            as *mut crate::leanh::LeanObject,
        482895969946473123 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 97, 115, 101, 65, 114, 103, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value)
            as *mut crate::leanh::LeanObject,
        14546932361418667927 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value)
            as *mut crate::leanh::LeanObject,
        8689124066155232629 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value:
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value:
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value:
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 110, 97, 109, 101, 73, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value)
            as *mut crate::leanh::LeanObject,
        17650298993540147476 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19_value:
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
    m_data: [114, 101, 110, 97, 109, 101, 95, 105, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [59, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_value)
            as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 100, 111, 116, 84, 107, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value)
            as *mut crate::leanh::LeanObject,
        10467776374279798389 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 103, 108, 111, 98, 97, 108, 32, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 108, 111, 99, 97, 108, 32, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 115, 116, 120, 32, 95, 32, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [78, 111, 32, 115, 112, 101, 99, 32, 109, 97, 116, 99, 104, 105, 110, 103, 32, 116, 104, 101, 32, 109, 111, 110, 97, 100, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [32, 102, 111, 117, 110, 100, 32, 102, 111, 114, 32, 112, 114, 111, 103, 114, 97, 109, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [46, 32, 67, 97, 110, 100, 105, 100, 97, 116, 101, 115, 32, 119, 101, 114, 101, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [78, 111, 32, 115, 112, 101, 99, 32, 102, 111, 117, 110, 100, 32, 102, 111, 114, 32, 112, 114, 111, 103, 114, 97, 109, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [68, 105, 100, 32, 110, 111, 116, 32, 107, 110, 111, 119, 32, 104, 111, 119, 32, 116, 111, 32, 100, 101, 99, 111, 109, 112, 111, 115, 101, 32, 119, 101, 97, 107, 101, 115, 116, 32, 112, 114, 101, 99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [118, 99, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 118, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0(
    mut v_x_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2886_);
    crate::leanh::lean_inc_ref(v___y_2885_);
    crate::leanh::lean_inc(v___y_2884_);
    crate::leanh::lean_inc_ref(v___y_2883_);
    crate::leanh::lean_inc(v___y_2882_);
    crate::leanh::lean_inc(v___y_2881_);
    crate::leanh::lean_inc_ref(v___y_2880_);
    v___x_2892_ = crate::leanh::lean_apply_12(
        v_x_2879_,
        v___y_2880_,
        v___y_2881_,
        v___y_2882_,
        v___y_2883_,
        v___y_2884_,
        v___y_2885_,
        v___y_2886_,
        v___y_2887_,
        v___y_2888_,
        v___y_2889_,
        v___y_2890_,
        crate::leanh::lean_box(0),
    );
    return v___x_2892_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0___boxed(
    mut v_x_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
    mut v___y_2902_: *mut crate::leanh::LeanObject,
    mut v___y_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2906_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0(v_x_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
    crate::leanh::lean_dec(v___y_2900_);
    crate::leanh::lean_dec_ref(v___y_2899_);
    crate::leanh::lean_dec(v___y_2898_);
    crate::leanh::lean_dec_ref(v___y_2897_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec(v___y_2895_);
    crate::leanh::lean_dec_ref(v___y_2894_);
    return v_res_2906_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(
    mut v_mvarId_2907_: *mut crate::leanh::LeanObject,
    mut v_x_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
    mut v___y_2916_: *mut crate::leanh::LeanObject,
    mut v___y_2917_: *mut crate::leanh::LeanObject,
    mut v___y_2918_: *mut crate::leanh::LeanObject,
    mut v___y_2919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2915_);
                crate::leanh::lean_inc_ref(v___y_2914_);
                crate::leanh::lean_inc(v___y_2913_);
                crate::leanh::lean_inc_ref(v___y_2912_);
                crate::leanh::lean_inc(v___y_2911_);
                crate::leanh::lean_inc(v___y_2910_);
                crate::leanh::lean_inc_ref(v___y_2909_);
                v___f_2921_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___f_2921_, 0, v_x_2908_);
                crate::leanh::lean_closure_set(v___f_2921_, 1, v___y_2909_);
                crate::leanh::lean_closure_set(v___f_2921_, 2, v___y_2910_);
                crate::leanh::lean_closure_set(v___f_2921_, 3, v___y_2911_);
                crate::leanh::lean_closure_set(v___f_2921_, 4, v___y_2912_);
                crate::leanh::lean_closure_set(v___f_2921_, 5, v___y_2913_);
                crate::leanh::lean_closure_set(v___f_2921_, 6, v___y_2914_);
                crate::leanh::lean_closure_set(v___f_2921_, 7, v___y_2915_);
                v___x_2922_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2907_,
                    v___f_2921_,
                    v___y_2916_,
                    v___y_2917_,
                    v___y_2918_,
                    v___y_2919_,
                );
                if crate::leanh::lean_obj_tag(v___x_2922_) == 0 {
                    return v___x_2922_;
                } else {
                    v_a_2923_ = crate::leanh::lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2930_ = (!crate::leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2930_ == 0 {
                        v___x_2925_ = v___x_2922_;
                        v_isShared_2926_ = v_isSharedCheck_2930_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2923_);
                        crate::leanh::lean_dec(v___x_2922_);
                        v___x_2925_ = crate::leanh::lean_box(0);
                        v_isShared_2926_ = v_isSharedCheck_2930_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2926_ == 0 {
                    v___x_2928_ = v___x_2925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
                    v___x_2928_ = v_reuseFailAlloc_2929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___boxed(
    mut v_mvarId_2931_: *mut crate::leanh::LeanObject,
    mut v_x_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
    mut v___y_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
    mut v___y_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_2931_, v_x_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
    crate::leanh::lean_dec(v___y_2943_);
    crate::leanh::lean_dec_ref(v___y_2942_);
    crate::leanh::lean_dec(v___y_2941_);
    crate::leanh::lean_dec_ref(v___y_2940_);
    crate::leanh::lean_dec(v___y_2939_);
    crate::leanh::lean_dec_ref(v___y_2938_);
    crate::leanh::lean_dec(v___y_2937_);
    crate::leanh::lean_dec_ref(v___y_2936_);
    crate::leanh::lean_dec(v___y_2935_);
    crate::leanh::lean_dec(v___y_2934_);
    crate::leanh::lean_dec_ref(v___y_2933_);
    return v_res_2945_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1(
    mut v_00_u03b1_2946_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2947_: *mut crate::leanh::LeanObject,
    mut v_x_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
    mut v___y_2954_: *mut crate::leanh::LeanObject,
    mut v___y_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_2947_, v_x_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
    return v___x_2961_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___boxed(
    mut v_00_u03b1_2962_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2963_: *mut crate::leanh::LeanObject,
    mut v_x_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
    mut v___y_2976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1(
            v_00_u03b1_2962_,
            v_mvarId_2963_,
            v_x_2964_,
            v___y_2965_,
            v___y_2966_,
            v___y_2967_,
            v___y_2968_,
            v___y_2969_,
            v___y_2970_,
            v___y_2971_,
            v___y_2972_,
            v___y_2973_,
            v___y_2974_,
            v___y_2975_,
        );
    crate::leanh::lean_dec(v___y_2975_);
    crate::leanh::lean_dec_ref(v___y_2974_);
    crate::leanh::lean_dec(v___y_2973_);
    crate::leanh::lean_dec_ref(v___y_2972_);
    crate::leanh::lean_dec(v___y_2971_);
    crate::leanh::lean_dec_ref(v___y_2970_);
    crate::leanh::lean_dec(v___y_2969_);
    crate::leanh::lean_dec_ref(v___y_2968_);
    crate::leanh::lean_dec(v___y_2967_);
    crate::leanh::lean_dec(v___y_2966_);
    crate::leanh::lean_dec_ref(v___y_2965_);
    return v_res_2977_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0(
    mut v_x_2978_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2979_: u8 = 0;
    v___x_2979_ = 0;
    return v___x_2979_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0___boxed(
    mut v_x_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2981_: u8 = 0;
    let mut v_r_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2981_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0(v_x_2980_);
    crate::leanh::lean_dec(v_x_2980_);
    v_r_2982_ = crate::leanh::lean_box((v_res_2981_) as usize);
    return v_r_2982_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(
    mut v_x_2983_: *mut crate::leanh::LeanObject,
    mut v_x_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
    mut v___y_2988_: *mut crate::leanh::LeanObject,
    mut v___y_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v_isSharedCheck_3016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2983_) == 0 {
                    v___x_2995_ = l_List_reverse___redArg(v_x_2984_);
                    v___x_2996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2995_);
                    return v___x_2996_;
                } else {
                    v_head_2997_ = crate::leanh::lean_ctor_get(v_x_2983_, 0);
                    v_tail_2998_ = crate::leanh::lean_ctor_get(v_x_2983_, 1);
                    v_isSharedCheck_3016_ = (!crate::leanh::lean_is_exclusive(v_x_2983_)) as u8;
                    if v_isSharedCheck_3016_ == 0 {
                        v___x_3000_ = v_x_2983_;
                        v_isShared_3001_ = v_isSharedCheck_3016_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2998_);
                        crate::leanh::lean_inc(v_head_2997_);
                        crate::leanh::lean_dec(v_x_2983_);
                        v___x_3000_ = crate::leanh::lean_box(0);
                        v_isShared_3001_ = v_isSharedCheck_3016_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3002_ = l_Lean_Meta_Grind_mkGoalCore(
                    v_head_2997_,
                    v___y_2985_,
                    v___y_2986_,
                    v___y_2987_,
                    v___y_2988_,
                    v___y_2989_,
                    v___y_2990_,
                    v___y_2991_,
                    v___y_2992_,
                    v___y_2993_,
                );
                if crate::leanh::lean_obj_tag(v___x_3002_) == 0 {
                    v_a_3003_ = crate::leanh::lean_ctor_get(v___x_3002_, 0);
                    crate::leanh::lean_inc(v_a_3003_);
                    crate::leanh::lean_dec_ref_known(v___x_3002_, 1);
                    if v_isShared_3001_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3000_, 1, v_x_2984_);
                        crate::leanh::lean_ctor_set(v___x_3000_, 0, v_a_3003_);
                        v___x_3005_ = v___x_3000_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3007_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3003_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_x_2984_);
                        v___x_3005_ = v_reuseFailAlloc_3007_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3000_);
                    crate::leanh::lean_dec(v_tail_2998_);
                    crate::leanh::lean_dec(v_x_2984_);
                    v_a_3008_ = crate::leanh::lean_ctor_get(v___x_3002_, 0);
                    v_isSharedCheck_3015_ = (!crate::leanh::lean_is_exclusive(v___x_3002_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_3010_ = v___x_3002_;
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3008_);
                        crate::leanh::lean_dec(v___x_3002_);
                        v___x_3010_ = crate::leanh::lean_box(0);
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_2983_ = v_tail_2998_;
                v_x_2984_ = v___x_3005_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3011_ == 0 {
                    v___x_3013_ = v___x_3010_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
                    v___x_3013_ = v_reuseFailAlloc_3014_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg___boxed(
    mut v_x_3017_: *mut crate::leanh::LeanObject,
    mut v_x_3018_: *mut crate::leanh::LeanObject,
    mut v___y_3019_: *mut crate::leanh::LeanObject,
    mut v___y_3020_: *mut crate::leanh::LeanObject,
    mut v___y_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
    mut v___y_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3029_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(
            v_x_3017_,
            v_x_3018_,
            v___y_3019_,
            v___y_3020_,
            v___y_3021_,
            v___y_3022_,
            v___y_3023_,
            v___y_3024_,
            v___y_3025_,
            v___y_3026_,
            v___y_3027_,
        );
    crate::leanh::lean_dec(v___y_3027_);
    crate::leanh::lean_dec_ref(v___y_3026_);
    crate::leanh::lean_dec(v___y_3025_);
    crate::leanh::lean_dec_ref(v___y_3024_);
    crate::leanh::lean_dec(v___y_3023_);
    crate::leanh::lean_dec_ref(v___y_3022_);
    crate::leanh::lean_dec(v___y_3021_);
    crate::leanh::lean_dec_ref(v___y_3020_);
    crate::leanh::lean_dec(v___y_3019_);
    return v_res_3029_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(
    mut v_msgData_3030_: *mut crate::leanh::LeanObject,
    mut v___y_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ = lean_st_ref_get(v___y_3034_);
    v_env_3037_ = crate::leanh::lean_ctor_get(v___x_3036_, 0);
    crate::leanh::lean_inc_ref(v_env_3037_);
    crate::leanh::lean_dec(v___x_3036_);
    v___x_3038_ = lean_st_ref_get(v___y_3032_);
    v_mctx_3039_ = crate::leanh::lean_ctor_get(v___x_3038_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3039_);
    crate::leanh::lean_dec(v___x_3038_);
    v_lctx_3040_ = crate::leanh::lean_ctor_get(v___y_3031_, 2);
    v_options_3041_ = crate::leanh::lean_ctor_get(v___y_3033_, 2);
    crate::leanh::lean_inc_ref(v_options_3041_);
    crate::leanh::lean_inc_ref(v_lctx_3040_);
    v___x_3042_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3042_, 0, v_env_3037_);
    crate::leanh::lean_ctor_set(v___x_3042_, 1, v_mctx_3039_);
    crate::leanh::lean_ctor_set(v___x_3042_, 2, v_lctx_3040_);
    crate::leanh::lean_ctor_set(v___x_3042_, 3, v_options_3041_);
    v___x_3043_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3043_, 0, v___x_3042_);
    crate::leanh::lean_ctor_set(v___x_3043_, 1, v_msgData_3030_);
    v___x_3044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_msgData_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v_msgData_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
    crate::leanh::lean_dec(v___y_3049_);
    crate::leanh::lean_dec_ref(v___y_3048_);
    crate::leanh::lean_dec(v___y_3047_);
    crate::leanh::lean_dec_ref(v___y_3046_);
    return v_res_3051_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5(
    mut v_opts_3052_: *mut crate::leanh::LeanObject,
    mut v_opt_3053_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3054_ = crate::leanh::lean_ctor_get(v_opt_3053_, 0);
    v_defValue_3055_ = crate::leanh::lean_ctor_get(v_opt_3053_, 1);
    v_map_3056_ = crate::leanh::lean_ctor_get(v_opts_3052_, 0);
    v___x_3057_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3056_,
            v_name_3054_,
        );
    if crate::leanh::lean_obj_tag(v___x_3057_) == 0 {
        let mut v___x_3058_: u8 = 0;
        v___x_3058_ = (crate::leanh::lean_unbox(v_defValue_3055_) as u8);
        return v___x_3058_;
    } else {
        let mut v_val_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3059_ = crate::leanh::lean_ctor_get(v___x_3057_, 0);
        crate::leanh::lean_inc(v_val_3059_);
        crate::leanh::lean_dec_ref_known(v___x_3057_, 1);
        if crate::leanh::lean_obj_tag(v_val_3059_) == 1 {
            let mut v_v_3060_: u8 = 0;
            v_v_3060_ = crate::leanh::lean_ctor_get_uint8(v_val_3059_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3059_, 0);
            return v_v_3060_;
        } else {
            let mut v___x_3061_: u8 = 0;
            crate::leanh::lean_dec(v_val_3059_);
            v___x_3061_ = (crate::leanh::lean_unbox(v_defValue_3055_) as u8);
            return v___x_3061_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_opts_3062_: *mut crate::leanh::LeanObject,
    mut v_opt_3063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3064_: u8 = 0;
    let mut v_r_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3064_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5(v_opts_3062_, v_opt_3063_);
    crate::leanh::lean_dec_ref(v_opt_3063_);
    crate::leanh::lean_dec_ref(v_opts_3062_);
    v_r_3065_ = crate::leanh::lean_box((v_res_3064_) as usize);
    return v_r_3065_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0(
    mut v___y_3074_: u8,
    mut v_suppressElabErrors_3075_: u8,
    mut v_x_3076_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3076_) == 1 {
        let mut v_pre_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_3077_ = crate::leanh::lean_ctor_get(v_x_3076_, 0);
        match crate::leanh::lean_obj_tag(v_pre_3077_) {
            1 => {
                let mut v_pre_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_3078_ = crate::leanh::lean_ctor_get(v_pre_3077_, 0);
                match crate::leanh::lean_obj_tag(v_pre_3078_) {
                    0 => {
                        let mut v_str_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3082_: u8 = 0;
                        v_str_3079_ = crate::leanh::lean_ctor_get(v_x_3076_, 1);
                        v_str_3080_ = crate::leanh::lean_ctor_get(v_pre_3077_, 1);
                        v___x_3081_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0;
                        v___x_3082_ = lean_string_dec_eq(v_str_3080_, v___x_3081_);
                        if v___x_3082_ == 0 {
                            let mut v___x_3083_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3084_: u8 = 0;
                            v___x_3083_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
                            v___x_3084_ = lean_string_dec_eq(v_str_3080_, v___x_3083_);
                            if v___x_3084_ == 0 {
                                return v___y_3074_;
                            } else {
                                let mut v___x_3085_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3086_: u8 = 0;
                                v___x_3085_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2;
                                v___x_3086_ = lean_string_dec_eq(v_str_3079_, v___x_3085_);
                                if v___x_3086_ == 0 {
                                    return v___y_3074_;
                                } else {
                                    return v_suppressElabErrors_3075_;
                                }
                            }
                        } else {
                            let mut v___x_3087_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3088_: u8 = 0;
                            v___x_3087_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3;
                            v___x_3088_ = lean_string_dec_eq(v_str_3079_, v___x_3087_);
                            if v___x_3088_ == 0 {
                                return v___y_3074_;
                            } else {
                                return v_suppressElabErrors_3075_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_3089_ = crate::leanh::lean_ctor_get(v_pre_3078_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3089_) == 0 {
                            let mut v_str_3090_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3091_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3092_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3093_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3094_: u8 = 0;
                            v_str_3090_ = crate::leanh::lean_ctor_get(v_x_3076_, 1);
                            v_str_3091_ = crate::leanh::lean_ctor_get(v_pre_3077_, 1);
                            v_str_3092_ = crate::leanh::lean_ctor_get(v_pre_3078_, 1);
                            v___x_3093_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4;
                            v___x_3094_ = lean_string_dec_eq(v_str_3092_, v___x_3093_);
                            if v___x_3094_ == 0 {
                                return v___y_3074_;
                            } else {
                                let mut v___x_3095_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3096_: u8 = 0;
                                v___x_3095_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5;
                                v___x_3096_ = lean_string_dec_eq(v_str_3091_, v___x_3095_);
                                if v___x_3096_ == 0 {
                                    return v___y_3074_;
                                } else {
                                    let mut v___x_3097_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3098_: u8 = 0;
                                    v___x_3097_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6;
                                    v___x_3098_ = lean_string_dec_eq(v_str_3090_, v___x_3097_);
                                    if v___x_3098_ == 0 {
                                        return v___y_3074_;
                                    } else {
                                        return v_suppressElabErrors_3075_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3074_;
                        }
                    }
                    _ => {
                        return v___y_3074_;
                    }
                }
            }
            0 => {
                let mut v_str_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3101_: u8 = 0;
                v_str_3099_ = crate::leanh::lean_ctor_get(v_x_3076_, 1);
                v___x_3100_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7;
                v___x_3101_ = lean_string_dec_eq(v_str_3099_, v___x_3100_);
                if v___x_3101_ == 0 {
                    return v___y_3074_;
                } else {
                    return v_suppressElabErrors_3075_;
                }
            }
            _ => {
                return v___y_3074_;
            }
        }
    } else {
        return v___y_3074_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___boxed(
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_3103_: *mut crate::leanh::LeanObject,
    mut v_x_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_42436__boxed_3105_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3106_: u8 = 0;
    let mut v_res_3107_: u8 = 0;
    let mut v_r_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_42436__boxed_3105_ = (crate::leanh::lean_unbox(v___y_3102_) as u8);
    v_suppressElabErrors_boxed_3106_ = (crate::leanh::lean_unbox(v_suppressElabErrors_3103_) as u8);
    v_res_3107_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0(v___y_42436__boxed_3105_, v_suppressElabErrors_boxed_3106_, v_x_3104_);
    crate::leanh::lean_dec(v_x_3104_);
    v_r_3108_ = crate::leanh::lean_box((v_res_3107_) as usize);
    return v_r_3108_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(
    mut v_ref_3110_: *mut crate::leanh::LeanObject,
    mut v_msgData_3111_: *mut crate::leanh::LeanObject,
    mut v_severity_3112_: u8,
    mut v_isSilent_3113_: u8,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3120_: u8 = 0;
    let mut v___y_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3124_: u8 = 0;
    let mut v___y_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut v___y_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: u8 = 0;
    let mut v___y_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: u8 = 0;
    let mut v___y_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: u8 = 0;
    let mut v___y_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v___y_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3182_: u8 = 0;
    let mut v___y_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: u8 = 0;
    let mut v___y_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: u8 = 0;
    let mut v___y_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3195_: u8 = 0;
    let mut v___y_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3197_: u8 = 0;
    let mut v___y_3198_: u8 = 0;
    let mut v_ref_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___y_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: u8 = 0;
    let mut v___y_3210_: u8 = 0;
    let mut v___y_3211_: u8 = 0;
    let mut v___y_3213_: u8 = 0;
    let mut v_fileName_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3218_: u8 = 0;
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u8 = 0;
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3203_ = 2;
                v___x_3228_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3112_, v___x_3203_);
                if v___x_3228_ == 0 {
                    v___y_3213_ = v___x_3228_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_3111_);
                    v___x_3229_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3111_);
                    v___y_3213_ = v___x_3229_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3129_ = lean_st_ref_take(v___y_3128_);
                v_currNamespace_3130_ = crate::leanh::lean_ctor_get(v___y_3127_, 6);
                v_openDecls_3131_ = crate::leanh::lean_ctor_get(v___y_3127_, 7);
                v_env_3132_ = crate::leanh::lean_ctor_get(v___x_3129_, 0);
                v_nextMacroScope_3133_ = crate::leanh::lean_ctor_get(v___x_3129_, 1);
                v_ngen_3134_ = crate::leanh::lean_ctor_get(v___x_3129_, 2);
                v_auxDeclNGen_3135_ = crate::leanh::lean_ctor_get(v___x_3129_, 3);
                v_traceState_3136_ = crate::leanh::lean_ctor_get(v___x_3129_, 4);
                v_cache_3137_ = crate::leanh::lean_ctor_get(v___x_3129_, 5);
                v_messages_3138_ = crate::leanh::lean_ctor_get(v___x_3129_, 6);
                v_infoState_3139_ = crate::leanh::lean_ctor_get(v___x_3129_, 7);
                v_snapshotTasks_3140_ = crate::leanh::lean_ctor_get(v___x_3129_, 8);
                v_isSharedCheck_3154_ = (!crate::leanh::lean_is_exclusive(v___x_3129_)) as u8;
                if v_isSharedCheck_3154_ == 0 {
                    v___x_3142_ = v___x_3129_;
                    v_isShared_3143_ = v_isSharedCheck_3154_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3140_);
                    crate::leanh::lean_inc(v_infoState_3139_);
                    crate::leanh::lean_inc(v_messages_3138_);
                    crate::leanh::lean_inc(v_cache_3137_);
                    crate::leanh::lean_inc(v_traceState_3136_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3135_);
                    crate::leanh::lean_inc(v_ngen_3134_);
                    crate::leanh::lean_inc(v_nextMacroScope_3133_);
                    crate::leanh::lean_inc(v_env_3132_);
                    crate::leanh::lean_dec(v___x_3129_);
                    v___x_3142_ = crate::leanh::lean_box(0);
                    v_isShared_3143_ = v_isSharedCheck_3154_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_3131_);
                crate::leanh::lean_inc(v_currNamespace_3130_);
                v___x_3144_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3144_, 0, v_currNamespace_3130_);
                crate::leanh::lean_ctor_set(v___x_3144_, 1, v_openDecls_3131_);
                v___x_3145_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3145_, 0, v___x_3144_);
                crate::leanh::lean_ctor_set(v___x_3145_, 1, v___y_3126_);
                crate::leanh::lean_inc_ref(v___y_3122_);
                crate::leanh::lean_inc_ref(v___y_3121_);
                v___x_3146_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_3146_, 0, v___y_3121_);
                crate::leanh::lean_ctor_set(v___x_3146_, 1, v___y_3123_);
                crate::leanh::lean_ctor_set(v___x_3146_, 2, v___y_3125_);
                crate::leanh::lean_ctor_set(v___x_3146_, 3, v___y_3122_);
                crate::leanh::lean_ctor_set(v___x_3146_, 4, v___x_3145_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3146_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3124_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3146_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_3120_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3146_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3113_,
                );
                v___x_3147_ = l_Lean_MessageLog_add(v___x_3146_, v_messages_3138_);
                if v_isShared_3143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3142_, 6, v___x_3147_);
                    v___x_3149_ = v___x_3142_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3153_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_env_3132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_nextMacroScope_3133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_ngen_3134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 3, v_auxDeclNGen_3135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 4, v_traceState_3136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 5, v_cache_3137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 6, v___x_3147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 7, v_infoState_3139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 8, v_snapshotTasks_3140_);
                    v___x_3149_ = v_reuseFailAlloc_3153_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3150_ = lean_st_ref_set(v___y_3128_, v___x_3149_);
                v___x_3151_ = crate::leanh::lean_box(0);
                v___x_3152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3151_);
                return v___x_3152_;
            }
            4 => {
                v___x_3164_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3111_,
                    );
                v___x_3165_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v___x_3164_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
                v_a_3166_ = crate::leanh::lean_ctor_get(v___x_3165_, 0);
                v_isSharedCheck_3179_ = (!crate::leanh::lean_is_exclusive(v___x_3165_)) as u8;
                if v_isSharedCheck_3179_ == 0 {
                    v___x_3168_ = v___x_3165_;
                    v_isShared_3169_ = v_isSharedCheck_3179_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3166_);
                    crate::leanh::lean_dec(v___x_3165_);
                    v___x_3168_ = crate::leanh::lean_box(0);
                    v_isShared_3169_ = v_isSharedCheck_3179_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_3161_, 2);
                v___x_3170_ = l_Lean_FileMap_toPosition(v___y_3161_, v___y_3157_);
                crate::leanh::lean_dec(v___y_3157_);
                v___x_3171_ = l_Lean_FileMap_toPosition(v___y_3161_, v___y_3163_);
                crate::leanh::lean_dec(v___y_3163_);
                v___x_3172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3172_, 0, v___x_3171_);
                v___x_3173_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0;
                if v___y_3162_ == 0 {
                    crate::leanh::lean_del_object(v___x_3168_);
                    crate::leanh::lean_dec_ref(v___y_3156_);
                    v___y_3120_ = v___y_3158_;
                    v___y_3121_ = v___y_3159_;
                    v___y_3122_ = v___x_3173_;
                    v___y_3123_ = v___x_3170_;
                    v___y_3124_ = v___y_3160_;
                    v___y_3125_ = v___x_3172_;
                    v___y_3126_ = v_a_3166_;
                    v___y_3127_ = v___y_3116_;
                    v___y_3128_ = v___y_3117_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3166_);
                    v___x_3174_ = l_Lean_MessageData_hasTag(v___y_3156_, v_a_3166_);
                    if v___x_3174_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3172_, 1);
                        crate::leanh::lean_dec_ref(v___x_3170_);
                        crate::leanh::lean_dec(v_a_3166_);
                        v___x_3175_ = crate::leanh::lean_box(0);
                        if v_isShared_3169_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3168_, 0, v___x_3175_);
                            v___x_3177_ = v___x_3168_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3178_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
                            v___x_3177_ = v_reuseFailAlloc_3178_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3168_);
                        v___y_3120_ = v___y_3158_;
                        v___y_3121_ = v___y_3159_;
                        v___y_3122_ = v___x_3173_;
                        v___y_3123_ = v___x_3170_;
                        v___y_3124_ = v___y_3160_;
                        v___y_3125_ = v___x_3172_;
                        v___y_3126_ = v_a_3166_;
                        v___y_3127_ = v___y_3116_;
                        v___y_3128_ = v___y_3117_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3177_;
            }
            7 => {
                v___x_3189_ = l_Lean_Syntax_getTailPos_x3f(v___y_3184_, v___y_3185_);
                crate::leanh::lean_dec(v___y_3184_);
                if crate::leanh::lean_obj_tag(v___x_3189_) == 0 {
                    crate::leanh::lean_inc(v___y_3188_);
                    v___y_3156_ = v___y_3181_;
                    v___y_3157_ = v___y_3188_;
                    v___y_3158_ = v___y_3182_;
                    v___y_3159_ = v___y_3183_;
                    v___y_3160_ = v___y_3185_;
                    v___y_3161_ = v___y_3186_;
                    v___y_3162_ = v___y_3187_;
                    v___y_3163_ = v___y_3188_;
                    state = 4;
                    continue;
                } else {
                    v_val_3190_ = crate::leanh::lean_ctor_get(v___x_3189_, 0);
                    crate::leanh::lean_inc(v_val_3190_);
                    crate::leanh::lean_dec_ref_known(v___x_3189_, 1);
                    v___y_3156_ = v___y_3181_;
                    v___y_3157_ = v___y_3188_;
                    v___y_3158_ = v___y_3182_;
                    v___y_3159_ = v___y_3183_;
                    v___y_3160_ = v___y_3185_;
                    v___y_3161_ = v___y_3186_;
                    v___y_3162_ = v___y_3187_;
                    v___y_3163_ = v_val_3190_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3199_ = l_Lean_replaceRef(v_ref_3110_, v___y_3194_);
                v___x_3200_ = l_Lean_Syntax_getPos_x3f(v_ref_3199_, v___y_3195_);
                if crate::leanh::lean_obj_tag(v___x_3200_) == 0 {
                    v___x_3201_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3181_ = v___y_3192_;
                    v___y_3182_ = v___y_3198_;
                    v___y_3183_ = v___y_3193_;
                    v___y_3184_ = v_ref_3199_;
                    v___y_3185_ = v___y_3195_;
                    v___y_3186_ = v___y_3196_;
                    v___y_3187_ = v___y_3197_;
                    v___y_3188_ = v___x_3201_;
                    state = 7;
                    continue;
                } else {
                    v_val_3202_ = crate::leanh::lean_ctor_get(v___x_3200_, 0);
                    crate::leanh::lean_inc(v_val_3202_);
                    crate::leanh::lean_dec_ref_known(v___x_3200_, 1);
                    v___y_3181_ = v___y_3192_;
                    v___y_3182_ = v___y_3198_;
                    v___y_3183_ = v___y_3193_;
                    v___y_3184_ = v_ref_3199_;
                    v___y_3185_ = v___y_3195_;
                    v___y_3186_ = v___y_3196_;
                    v___y_3187_ = v___y_3197_;
                    v___y_3188_ = v_val_3202_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3211_ == 0 {
                    v___y_3192_ = v___y_3207_;
                    v___y_3193_ = v___y_3205_;
                    v___y_3194_ = v___y_3206_;
                    v___y_3195_ = v___y_3210_;
                    v___y_3196_ = v___y_3208_;
                    v___y_3197_ = v___y_3209_;
                    v___y_3198_ = v_severity_3112_;
                    state = 8;
                    continue;
                } else {
                    v___y_3192_ = v___y_3207_;
                    v___y_3193_ = v___y_3205_;
                    v___y_3194_ = v___y_3206_;
                    v___y_3195_ = v___y_3210_;
                    v___y_3196_ = v___y_3208_;
                    v___y_3197_ = v___y_3209_;
                    v___y_3198_ = v___x_3203_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3213_ == 0 {
                    v_fileName_3214_ = crate::leanh::lean_ctor_get(v___y_3116_, 0);
                    v_fileMap_3215_ = crate::leanh::lean_ctor_get(v___y_3116_, 1);
                    v_options_3216_ = crate::leanh::lean_ctor_get(v___y_3116_, 2);
                    v_ref_3217_ = crate::leanh::lean_ctor_get(v___y_3116_, 5);
                    v_suppressElabErrors_3218_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3116_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3219_ = crate::leanh::lean_box((v___y_3213_) as usize);
                    v___x_3220_ = crate::leanh::lean_box((v_suppressElabErrors_3218_) as usize);
                    v___f_3221_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_3221_, 0, v___x_3219_);
                    crate::leanh::lean_closure_set(v___f_3221_, 1, v___x_3220_);
                    v___x_3222_ = 1;
                    v___x_3223_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3112_, v___x_3222_);
                    if v___x_3223_ == 0 {
                        v___y_3205_ = v_fileName_3214_;
                        v___y_3206_ = v_ref_3217_;
                        v___y_3207_ = v___f_3221_;
                        v___y_3208_ = v_fileMap_3215_;
                        v___y_3209_ = v_suppressElabErrors_3218_;
                        v___y_3210_ = v___y_3213_;
                        v___y_3211_ = v___x_3223_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3224_ = l_Lean_warningAsError;
                        v___x_3225_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5(v_options_3216_, v___x_3224_);
                        v___y_3205_ = v_fileName_3214_;
                        v___y_3206_ = v_ref_3217_;
                        v___y_3207_ = v___f_3221_;
                        v___y_3208_ = v_fileMap_3215_;
                        v___y_3209_ = v_suppressElabErrors_3218_;
                        v___y_3210_ = v___y_3213_;
                        v___y_3211_ = v___x_3225_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_3111_);
                    v___x_3226_ = crate::leanh::lean_box(0);
                    v___x_3227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3227_, 0, v___x_3226_);
                    return v___x_3227_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_3230_: *mut crate::leanh::LeanObject,
    mut v_msgData_3231_: *mut crate::leanh::LeanObject,
    mut v_severity_3232_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3239_: u8 = 0;
    let mut v_isSilent_boxed_3240_: u8 = 0;
    let mut v_res_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3239_ = (crate::leanh::lean_unbox(v_severity_3232_) as u8);
    v_isSilent_boxed_3240_ = (crate::leanh::lean_unbox(v_isSilent_3233_) as u8);
    v_res_3241_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_3230_, v_msgData_3231_, v_severity_boxed_3239_, v_isSilent_boxed_3240_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
    crate::leanh::lean_dec(v___y_3237_);
    crate::leanh::lean_dec_ref(v___y_3236_);
    crate::leanh::lean_dec(v___y_3235_);
    crate::leanh::lean_dec_ref(v___y_3234_);
    crate::leanh::lean_dec(v_ref_3230_);
    return v_res_3241_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(
    mut v_msgData_3242_: *mut crate::leanh::LeanObject,
    mut v_severity_3243_: u8,
    mut v_isSilent_3244_: u8,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3257_ = crate::leanh::lean_ctor_get(v___y_3254_, 5);
    v___x_3258_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_3257_, v_msgData_3242_, v_severity_3243_, v_isSilent_3244_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
    return v___x_3258_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0___boxed(
    mut v_msgData_3259_: *mut crate::leanh::LeanObject,
    mut v_severity_3260_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3261_: *mut crate::leanh::LeanObject,
    mut v___y_3262_: *mut crate::leanh::LeanObject,
    mut v___y_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3274_: u8 = 0;
    let mut v_isSilent_boxed_3275_: u8 = 0;
    let mut v_res_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3274_ = (crate::leanh::lean_unbox(v_severity_3260_) as u8);
    v_isSilent_boxed_3275_ = (crate::leanh::lean_unbox(v_isSilent_3261_) as u8);
    v_res_3276_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(v_msgData_3259_, v_severity_boxed_3274_, v_isSilent_boxed_3275_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
    crate::leanh::lean_dec(v___y_3272_);
    crate::leanh::lean_dec_ref(v___y_3271_);
    crate::leanh::lean_dec(v___y_3270_);
    crate::leanh::lean_dec_ref(v___y_3269_);
    crate::leanh::lean_dec(v___y_3268_);
    crate::leanh::lean_dec_ref(v___y_3267_);
    crate::leanh::lean_dec(v___y_3266_);
    crate::leanh::lean_dec_ref(v___y_3265_);
    crate::leanh::lean_dec(v___y_3264_);
    crate::leanh::lean_dec(v___y_3263_);
    crate::leanh::lean_dec_ref(v___y_3262_);
    return v_res_3276_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0(
    mut v_msgData_3277_: *mut crate::leanh::LeanObject,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
    mut v___y_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ = 2;
    v___x_3291_ = 0;
    v___x_3292_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(v_msgData_3277_, v___x_3290_, v___x_3291_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
    return v___x_3292_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0___boxed(
    mut v_msgData_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
    mut v___y_3295_: *mut crate::leanh::LeanObject,
    mut v___y_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___y_3302_: *mut crate::leanh::LeanObject,
    mut v___y_3303_: *mut crate::leanh::LeanObject,
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0(
        v_msgData_3293_,
        v___y_3294_,
        v___y_3295_,
        v___y_3296_,
        v___y_3297_,
        v___y_3298_,
        v___y_3299_,
        v___y_3300_,
        v___y_3301_,
        v___y_3302_,
        v___y_3303_,
        v___y_3304_,
    );
    crate::leanh::lean_dec(v___y_3304_);
    crate::leanh::lean_dec_ref(v___y_3303_);
    crate::leanh::lean_dec(v___y_3302_);
    crate::leanh::lean_dec_ref(v___y_3301_);
    crate::leanh::lean_dec(v___y_3300_);
    crate::leanh::lean_dec_ref(v___y_3299_);
    crate::leanh::lean_dec(v___y_3298_);
    crate::leanh::lean_dec_ref(v___y_3297_);
    crate::leanh::lean_dec(v___y_3296_);
    crate::leanh::lean_dec(v___y_3295_);
    crate::leanh::lean_dec_ref(v___y_3294_);
    return v_res_3306_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3308_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0;
    v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
    return v___x_3309_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(
    mut v_x_3324_: *mut crate::leanh::LeanObject,
    mut v_x_3325_: *mut crate::leanh::LeanObject,
    mut v_a_3326_: *mut crate::leanh::LeanObject,
    mut v_a_3327_: *mut crate::leanh::LeanObject,
    mut v_a_3328_: *mut crate::leanh::LeanObject,
    mut v_a_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_silent_3345_: u8 = 0;
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3354_: u8 = 0;
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3386_: u8 = 0;
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut v_a_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_reuseFailAlloc_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v_unused_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3404_: u8 = 0;
    let mut v_unused_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut v_a_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut v_tac_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3324_) {
                0 => {
                    v___x_3342_ = crate::leanh::lean_box(0);
                    v___x_3343_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3343_, 0, v_x_3325_);
                    crate::leanh::lean_ctor_set(v___x_3343_, 1, v___x_3342_);
                    v___x_3344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3344_, 0, v___x_3343_);
                    return v___x_3344_;
                }
                1 => {
                    v_silent_3345_ = crate::leanh::lean_ctor_get_uint8(v_x_3324_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_x_3324_, 0);
                    v___x_3346_ = lean_st_ref_get(v_a_3334_);
                    crate::leanh::lean_inc_ref(v_x_3325_);
                    v___x_3347_ = l_Lean_Meta_Grind_Goal_grind(
                        v_x_3325_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_,
                        v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3347_) == 0 {
                        v_a_3348_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                        v_isSharedCheck_3410_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3347_)) as u8;
                        if v_isSharedCheck_3410_ == 0 {
                            v___x_3350_ = v___x_3347_;
                            v_isShared_3351_ = v_isSharedCheck_3410_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3348_);
                            crate::leanh::lean_dec(v___x_3347_);
                            v___x_3350_ = crate::leanh::lean_box(0);
                            v_isShared_3351_ = v_isSharedCheck_3410_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3346_);
                        crate::leanh::lean_dec_ref(v_x_3325_);
                        v_a_3411_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                        v_isSharedCheck_3418_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3347_)) as u8;
                        if v_isSharedCheck_3418_ == 0 {
                            v___x_3413_ = v___x_3347_;
                            v_isShared_3414_ = v_isSharedCheck_3418_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3411_);
                            crate::leanh::lean_dec(v___x_3347_);
                            v___x_3413_ = crate::leanh::lean_box(0);
                            v_isShared_3414_ = v_isSharedCheck_3418_;
                            state = 12;
                            continue;
                        }
                    }
                }
                _ => {
                    v_tac_3419_ = crate::leanh::lean_ctor_get(v_x_3324_, 0);
                    crate::leanh::lean_inc(v_tac_3419_);
                    crate::leanh::lean_dec_ref_known(v_x_3324_, 1);
                    v_mvarId_3420_ = crate::leanh::lean_ctor_get(v_x_3325_, 1);
                    crate::leanh::lean_inc(v_mvarId_3420_);
                    crate::leanh::lean_dec_ref(v_x_3325_);
                    v___x_3421_ = crate::leanh::lean_box(0);
                    v___x_3422_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4;
                    v___x_3423_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5;
                    v___x_3424_ = l_Lean_Elab_runTactic(
                        v_mvarId_3420_,
                        v_tac_3419_,
                        v___x_3422_,
                        v___x_3423_,
                        v_a_3333_,
                        v_a_3334_,
                        v_a_3335_,
                        v_a_3336_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3424_) == 0 {
                        v_a_3425_ = crate::leanh::lean_ctor_get(v___x_3424_, 0);
                        crate::leanh::lean_inc(v_a_3425_);
                        crate::leanh::lean_dec_ref_known(v___x_3424_, 1);
                        v_fst_3426_ = crate::leanh::lean_ctor_get(v_a_3425_, 0);
                        crate::leanh::lean_inc(v_fst_3426_);
                        crate::leanh::lean_dec(v_a_3425_);
                        v___x_3427_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(v_fst_3426_, v___x_3421_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
                        return v___x_3427_;
                    } else {
                        v_a_3428_ = crate::leanh::lean_ctor_get(v___x_3424_, 0);
                        v_isSharedCheck_3435_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3424_)) as u8;
                        if v_isSharedCheck_3435_ == 0 {
                            v___x_3430_ = v___x_3424_;
                            v_isShared_3431_ = v_isSharedCheck_3435_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3428_);
                            crate::leanh::lean_dec(v___x_3424_);
                            v___x_3430_ = crate::leanh::lean_box(0);
                            v_isShared_3431_ = v_isSharedCheck_3435_;
                            state = 14;
                            continue;
                        }
                    }
                }
            },
            1 => {
                v___x_3339_ = crate::leanh::lean_box(0);
                v___x_3340_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3340_, 0, v_x_3325_);
                crate::leanh::lean_ctor_set(v___x_3340_, 1, v___x_3339_);
                v___x_3341_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3341_, 0, v___x_3340_);
                return v___x_3341_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3348_) == 0 {
                    crate::leanh::lean_del_object(v___x_3350_);
                    v_isSharedCheck_3404_ = (!crate::leanh::lean_is_exclusive(v_a_3348_)) as u8;
                    if v_isSharedCheck_3404_ == 0 {
                        v_unused_3405_ = crate::leanh::lean_ctor_get(v_a_3348_, 0);
                        crate::leanh::lean_dec(v_unused_3405_);
                        v___x_3353_ = v_a_3348_;
                        v_isShared_3354_ = v_isSharedCheck_3404_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3348_);
                        v___x_3353_ = crate::leanh::lean_box(0);
                        v_isShared_3354_ = v_isSharedCheck_3404_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3346_);
                    crate::leanh::lean_dec_ref(v_x_3325_);
                    v___x_3406_ = crate::leanh::lean_box(0);
                    if v_isShared_3351_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3350_, 0, v___x_3406_);
                        v___x_3408_ = v___x_3350_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
                        v___x_3408_ = v_reuseFailAlloc_3409_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3355_ = lean_st_ref_take(v_a_3334_);
                v_mctx_3356_ = crate::leanh::lean_ctor_get(v___x_3346_, 0);
                crate::leanh::lean_inc_ref(v_mctx_3356_);
                crate::leanh::lean_dec(v___x_3346_);
                v_cache_3357_ = crate::leanh::lean_ctor_get(v___x_3355_, 1);
                v_zetaDeltaFVarIds_3358_ = crate::leanh::lean_ctor_get(v___x_3355_, 2);
                v_postponed_3359_ = crate::leanh::lean_ctor_get(v___x_3355_, 3);
                v_diag_3360_ = crate::leanh::lean_ctor_get(v___x_3355_, 4);
                v_isSharedCheck_3402_ = (!crate::leanh::lean_is_exclusive(v___x_3355_)) as u8;
                if v_isSharedCheck_3402_ == 0 {
                    v_unused_3403_ = crate::leanh::lean_ctor_get(v___x_3355_, 0);
                    crate::leanh::lean_dec(v_unused_3403_);
                    v___x_3362_ = v___x_3355_;
                    v_isShared_3363_ = v_isSharedCheck_3402_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3360_);
                    crate::leanh::lean_inc(v_postponed_3359_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3358_);
                    crate::leanh::lean_inc(v_cache_3357_);
                    crate::leanh::lean_dec(v___x_3355_);
                    v___x_3362_ = crate::leanh::lean_box(0);
                    v_isShared_3363_ = v_isSharedCheck_3402_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3362_, 0, v_mctx_3356_);
                    v___x_3365_ = v___x_3362_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3401_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_mctx_3356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_cache_3357_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3401_,
                        2,
                        v_zetaDeltaFVarIds_3358_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 3, v_postponed_3359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3401_, 4, v_diag_3360_);
                    v___x_3365_ = v_reuseFailAlloc_3401_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3366_ = lean_st_ref_set(v_a_3334_, v___x_3365_);
                if v_silent_3345_ == 0 {
                    v_mvarId_3367_ = crate::leanh::lean_ctor_get(v_x_3325_, 1);
                    v___x_3368_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1,
                    );
                    crate::leanh::lean_inc(v_mvarId_3367_);
                    if v_isShared_3354_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3353_, 1);
                        crate::leanh::lean_ctor_set(v___x_3353_, 0, v_mvarId_3367_);
                        v___x_3370_ = v___x_3353_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_mvarId_3367_);
                        v___x_3370_ = v_reuseFailAlloc_3400_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3353_);
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_3371_ = l_Lean_indentD(v___x_3370_);
                v___x_3372_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3372_, 0, v___x_3368_);
                crate::leanh::lean_ctor_set(v___x_3372_, 1, v___x_3371_);
                v___x_3373_ = crate::leanh::lean_alloc_closure(l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0___boxed as *mut core::ffi::c_void, 13, 1);
                crate::leanh::lean_closure_set(v___x_3373_, 0, v___x_3372_);
                crate::leanh::lean_inc(v_mvarId_3367_);
                v___x_3374_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_3367_, v___x_3373_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
                if crate::leanh::lean_obj_tag(v___x_3374_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3374_, 1);
                    v___x_3375_ = lean_st_ref_take(v_a_3327_);
                    v_specBackwardRuleCache_3376_ = crate::leanh::lean_ctor_get(v___x_3375_, 0);
                    v_splitBackwardRuleCache_3377_ = crate::leanh::lean_ctor_get(v___x_3375_, 1);
                    v_invariants_3378_ = crate::leanh::lean_ctor_get(v___x_3375_, 2);
                    v_vcs_3379_ = crate::leanh::lean_ctor_get(v___x_3375_, 3);
                    v_simpState_3380_ = crate::leanh::lean_ctor_get(v___x_3375_, 4);
                    v_fuel_3381_ = crate::leanh::lean_ctor_get(v___x_3375_, 5);
                    v_inlineHandledInvariants_3382_ = crate::leanh::lean_ctor_get(v___x_3375_, 6);
                    v_isSharedCheck_3391_ = (!crate::leanh::lean_is_exclusive(v___x_3375_)) as u8;
                    if v_isSharedCheck_3391_ == 0 {
                        v___x_3384_ = v___x_3375_;
                        v_isShared_3385_ = v_isSharedCheck_3391_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_inlineHandledInvariants_3382_);
                        crate::leanh::lean_inc(v_fuel_3381_);
                        crate::leanh::lean_inc(v_simpState_3380_);
                        crate::leanh::lean_inc(v_vcs_3379_);
                        crate::leanh::lean_inc(v_invariants_3378_);
                        crate::leanh::lean_inc(v_splitBackwardRuleCache_3377_);
                        crate::leanh::lean_inc(v_specBackwardRuleCache_3376_);
                        crate::leanh::lean_dec(v___x_3375_);
                        v___x_3384_ = crate::leanh::lean_box(0);
                        v_isShared_3385_ = v_isSharedCheck_3391_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3325_);
                    v_a_3392_ = crate::leanh::lean_ctor_get(v___x_3374_, 0);
                    v_isSharedCheck_3399_ = (!crate::leanh::lean_is_exclusive(v___x_3374_)) as u8;
                    if v_isSharedCheck_3399_ == 0 {
                        v___x_3394_ = v___x_3374_;
                        v_isShared_3395_ = v_isSharedCheck_3399_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3392_);
                        crate::leanh::lean_dec(v___x_3374_);
                        v___x_3394_ = crate::leanh::lean_box(0);
                        v_isShared_3395_ = v_isSharedCheck_3399_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3386_ = 1;
                if v_isShared_3385_ == 0 {
                    v___x_3388_ = v___x_3384_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3390_,
                        0,
                        v_specBackwardRuleCache_3376_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3390_,
                        1,
                        v_splitBackwardRuleCache_3377_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_invariants_3378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_vcs_3379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_simpState_3380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 5, v_fuel_3381_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3390_,
                        6,
                        v_inlineHandledInvariants_3382_,
                    );
                    v___x_3388_ = v_reuseFailAlloc_3390_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3388_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_3386_,
                );
                v___x_3389_ = lean_st_ref_set(v_a_3327_, v___x_3388_);
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_3395_ == 0 {
                    v___x_3397_ = v___x_3394_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
                    v___x_3397_ = v_reuseFailAlloc_3398_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3397_;
            }
            11 => {
                return v___x_3408_;
            }
            12 => {
                if v_isShared_3414_ == 0 {
                    v___x_3416_ = v___x_3413_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
                    v___x_3416_ = v_reuseFailAlloc_3417_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3416_;
            }
            14 => {
                if v_isShared_3431_ == 0 {
                    v___x_3433_ = v___x_3430_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
                    v___x_3433_ = v_reuseFailAlloc_3434_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___boxed(
    mut v_x_3436_: *mut crate::leanh::LeanObject,
    mut v_x_3437_: *mut crate::leanh::LeanObject,
    mut v_a_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
    mut v_a_3440_: *mut crate::leanh::LeanObject,
    mut v_a_3441_: *mut crate::leanh::LeanObject,
    mut v_a_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
    mut v_a_3448_: *mut crate::leanh::LeanObject,
    mut v_a_3449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3450_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(
        v_x_3436_, v_x_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_,
        v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_,
    );
    crate::leanh::lean_dec(v_a_3448_);
    crate::leanh::lean_dec_ref(v_a_3447_);
    crate::leanh::lean_dec(v_a_3446_);
    crate::leanh::lean_dec_ref(v_a_3445_);
    crate::leanh::lean_dec(v_a_3444_);
    crate::leanh::lean_dec_ref(v_a_3443_);
    crate::leanh::lean_dec(v_a_3442_);
    crate::leanh::lean_dec_ref(v_a_3441_);
    crate::leanh::lean_dec(v_a_3440_);
    crate::leanh::lean_dec(v_a_3439_);
    crate::leanh::lean_dec_ref(v_a_3438_);
    return v_res_3450_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2(
    mut v_x_3451_: *mut crate::leanh::LeanObject,
    mut v_x_3452_: *mut crate::leanh::LeanObject,
    mut v___y_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
    mut v___y_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
    mut v___y_3461_: *mut crate::leanh::LeanObject,
    mut v___y_3462_: *mut crate::leanh::LeanObject,
    mut v___y_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ =
        l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(
            v_x_3451_,
            v_x_3452_,
            v___y_3455_,
            v___y_3456_,
            v___y_3457_,
            v___y_3458_,
            v___y_3459_,
            v___y_3460_,
            v___y_3461_,
            v___y_3462_,
            v___y_3463_,
        );
    return v___x_3465_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___boxed(
    mut v_x_3466_: *mut crate::leanh::LeanObject,
    mut v_x_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2(
        v_x_3466_,
        v_x_3467_,
        v___y_3468_,
        v___y_3469_,
        v___y_3470_,
        v___y_3471_,
        v___y_3472_,
        v___y_3473_,
        v___y_3474_,
        v___y_3475_,
        v___y_3476_,
        v___y_3477_,
        v___y_3478_,
    );
    crate::leanh::lean_dec(v___y_3478_);
    crate::leanh::lean_dec_ref(v___y_3477_);
    crate::leanh::lean_dec(v___y_3476_);
    crate::leanh::lean_dec_ref(v___y_3475_);
    crate::leanh::lean_dec(v___y_3474_);
    crate::leanh::lean_dec_ref(v___y_3473_);
    crate::leanh::lean_dec(v___y_3472_);
    crate::leanh::lean_dec_ref(v___y_3471_);
    crate::leanh::lean_dec(v___y_3470_);
    crate::leanh::lean_dec(v___y_3469_);
    crate::leanh::lean_dec_ref(v___y_3468_);
    return v_res_3480_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(
    mut v_ref_3481_: *mut crate::leanh::LeanObject,
    mut v_msgData_3482_: *mut crate::leanh::LeanObject,
    mut v_severity_3483_: u8,
    mut v_isSilent_3484_: u8,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v___y_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3497_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_3481_, v_msgData_3482_, v_severity_3483_, v_isSilent_3484_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
    return v___x_3497_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___boxed(
    mut v_ref_3498_: *mut crate::leanh::LeanObject,
    mut v_msgData_3499_: *mut crate::leanh::LeanObject,
    mut v_severity_3500_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
    mut v___y_3504_: *mut crate::leanh::LeanObject,
    mut v___y_3505_: *mut crate::leanh::LeanObject,
    mut v___y_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3514_: u8 = 0;
    let mut v_isSilent_boxed_3515_: u8 = 0;
    let mut v_res_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3514_ = (crate::leanh::lean_unbox(v_severity_3500_) as u8);
    v_isSilent_boxed_3515_ = (crate::leanh::lean_unbox(v_isSilent_3501_) as u8);
    v_res_3516_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(v_ref_3498_, v_msgData_3499_, v_severity_boxed_3514_, v_isSilent_boxed_3515_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
    crate::leanh::lean_dec(v___y_3512_);
    crate::leanh::lean_dec_ref(v___y_3511_);
    crate::leanh::lean_dec(v___y_3510_);
    crate::leanh::lean_dec_ref(v___y_3509_);
    crate::leanh::lean_dec(v___y_3508_);
    crate::leanh::lean_dec_ref(v___y_3507_);
    crate::leanh::lean_dec(v___y_3506_);
    crate::leanh::lean_dec_ref(v___y_3505_);
    crate::leanh::lean_dec(v___y_3504_);
    crate::leanh::lean_dec(v___y_3503_);
    crate::leanh::lean_dec_ref(v___y_3502_);
    crate::leanh::lean_dec(v_ref_3498_);
    return v_res_3516_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(
    mut v_mvarId_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = lean_st_ref_get(v___y_3518_);
    v_mctx_3521_ = crate::leanh::lean_ctor_get(v___x_3520_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3521_);
    crate::leanh::lean_dec(v___x_3520_);
    v___x_3522_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_3521_, v_mvarId_3517_);
    crate::leanh::lean_dec_ref(v_mctx_3521_);
    v___x_3523_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3523_, 0, v___x_3522_);
    return v___x_3523_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg___boxed(
    mut v_mvarId_3524_: *mut crate::leanh::LeanObject,
    mut v___y_3525_: *mut crate::leanh::LeanObject,
    mut v___y_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mvarId_3524_, v___y_3525_);
    crate::leanh::lean_dec(v___y_3525_);
    crate::leanh::lean_dec(v_mvarId_3524_);
    return v_res_3527_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(
    mut v_mvarId_3528_: *mut crate::leanh::LeanObject,
    mut v___y_3529_: *mut crate::leanh::LeanObject,
    mut v___y_3530_: *mut crate::leanh::LeanObject,
    mut v___y_3531_: *mut crate::leanh::LeanObject,
    mut v___y_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
    mut v___y_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3536_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mvarId_3528_, v___y_3532_);
    return v___x_3536_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___boxed(
    mut v_mvarId_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
    mut v___y_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3545_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(v_mvarId_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
    crate::leanh::lean_dec(v___y_3543_);
    crate::leanh::lean_dec_ref(v___y_3542_);
    crate::leanh::lean_dec(v___y_3541_);
    crate::leanh::lean_dec_ref(v___y_3540_);
    crate::leanh::lean_dec(v___y_3539_);
    crate::leanh::lean_dec_ref(v___y_3538_);
    crate::leanh::lean_dec(v_mvarId_3537_);
    return v_res_3545_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_keys_3546_: *mut crate::leanh::LeanObject,
    mut v_i_3547_: *mut crate::leanh::LeanObject,
    mut v_k_3548_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: u8 = 0;
    let mut v_k_x27_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: u8 = 0;
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3549_ = lean_array_get_size(v_keys_3546_);
                v___x_3550_ = lean_nat_dec_lt(v_i_3547_, v___x_3549_);
                if v___x_3550_ == 0 {
                    crate::leanh::lean_dec(v_i_3547_);
                    return v___x_3550_;
                } else {
                    v_k_x27_3551_ = lean_array_fget_borrowed(v_keys_3546_, v_i_3547_);
                    v___x_3552_ = l_Lean_instBEqMVarId_beq(v_k_3548_, v_k_x27_3551_);
                    if v___x_3552_ == 0 {
                        v___x_3553_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3554_ = lean_nat_add(v_i_3547_, v___x_3553_);
                        crate::leanh::lean_dec(v_i_3547_);
                        v_i_3547_ = v___x_3554_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_3547_);
                        return v___x_3552_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_keys_3556_: *mut crate::leanh::LeanObject,
    mut v_i_3557_: *mut crate::leanh::LeanObject,
    mut v_k_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_3556_, v_i_3557_, v_k_3558_);
    crate::leanh::lean_dec(v_k_3558_);
    crate::leanh::lean_dec_ref(v_keys_3556_);
    v_r_3560_ = crate::leanh::lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_3561_: usize = 0;
    let mut v___x_3562_: usize = 0;
    let mut v___x_3563_: usize = 0;
    v___x_3561_ = 5usize;
    v___x_3562_ = 1usize;
    v___x_3563_ = lean_usize_shift_left(v___x_3562_, v___x_3561_);
    return v___x_3563_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_3564_: usize = 0;
    let mut v___x_3565_: usize = 0;
    let mut v___x_3566_: usize = 0;
    v___x_3564_ = 1usize;
    v___x_3565_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0);
    v___x_3566_ = lean_usize_sub(v___x_3565_, v___x_3564_);
    return v___x_3566_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(
    mut v_x_3567_: *mut crate::leanh::LeanObject,
    mut v_x_3568_: usize,
    mut v_x_3569_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: usize = 0;
    let mut v___x_3573_: usize = 0;
    let mut v___x_3574_: usize = 0;
    let mut v_j_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: u8 = 0;
    let mut v_node_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: usize = 0;
    let mut v___x_3582_: u8 = 0;
    let mut v_ks_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3567_) == 0 {
                    v_es_3570_ = crate::leanh::lean_ctor_get(v_x_3567_, 0);
                    v___x_3571_ = crate::leanh::lean_box(2);
                    v___x_3572_ = 5usize;
                    v___x_3573_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_3574_ = lean_usize_land(v_x_3568_, v___x_3573_);
                    v_j_3575_ = lean_usize_to_nat(v___x_3574_);
                    v___x_3576_ = lean_array_get_borrowed(v___x_3571_, v_es_3570_, v_j_3575_);
                    crate::leanh::lean_dec(v_j_3575_);
                    match crate::leanh::lean_obj_tag(v___x_3576_) {
                        0 => {
                            v_key_3577_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                            v___x_3578_ = l_Lean_instBEqMVarId_beq(v_x_3569_, v_key_3577_);
                            return v___x_3578_;
                        }
                        1 => {
                            v_node_3579_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                            v___x_3580_ = lean_usize_shift_right(v_x_3568_, v___x_3572_);
                            v_x_3567_ = v_node_3579_;
                            v_x_3568_ = v___x_3580_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3582_ = 0;
                            return v___x_3582_;
                        }
                    }
                } else {
                    v_ks_3583_ = crate::leanh::lean_ctor_get(v_x_3567_, 0);
                    v___x_3584_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3585_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_3583_, v___x_3584_, v_x_3569_);
                    return v___x_3585_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_x_3586_: *mut crate::leanh::LeanObject,
    mut v_x_3587_: *mut crate::leanh::LeanObject,
    mut v_x_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17592__boxed_3589_: usize = 0;
    let mut v_res_3590_: u8 = 0;
    let mut v_r_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17592__boxed_3589_ = crate::leanh::lean_unbox_usize(v_x_3587_);
    crate::leanh::lean_dec(v_x_3587_);
    v_res_3590_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_3586_, v_x_17592__boxed_3589_, v_x_3588_);
    crate::leanh::lean_dec(v_x_3588_);
    crate::leanh::lean_dec_ref(v_x_3586_);
    v_r_3591_ = crate::leanh::lean_box((v_res_3590_) as usize);
    return v_r_3591_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(
    mut v_x_3592_: *mut crate::leanh::LeanObject,
    mut v_x_3593_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3594_: u64 = 0;
    let mut v___x_3595_: usize = 0;
    let mut v___x_3596_: u8 = 0;
    v___x_3594_ = l_Lean_instHashableMVarId_hash(v_x_3593_);
    v___x_3595_ = lean_uint64_to_usize(v___x_3594_);
    v___x_3596_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_3592_, v___x_3595_, v_x_3593_);
    return v___x_3596_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(
    mut v_x_3597_: *mut crate::leanh::LeanObject,
    mut v_x_3598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3599_: u8 = 0;
    let mut v_r_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_3597_, v_x_3598_);
    crate::leanh::lean_dec(v_x_3598_);
    crate::leanh::lean_dec_ref(v_x_3597_);
    v_r_3600_ = crate::leanh::lean_box((v_res_3599_) as usize);
    return v_r_3600_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(
    mut v_mvarId_3601_: *mut crate::leanh::LeanObject,
    mut v___y_3602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3604_ = lean_st_ref_get(v___y_3602_);
    v_mctx_3605_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3605_);
    crate::leanh::lean_dec(v___x_3604_);
    v_eAssignment_3606_ = crate::leanh::lean_ctor_get(v_mctx_3605_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_3606_);
    crate::leanh::lean_dec_ref(v_mctx_3605_);
    v___x_3607_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_3606_, v_mvarId_3601_);
    crate::leanh::lean_dec_ref(v_eAssignment_3606_);
    v___x_3608_ = crate::leanh::lean_box((v___x_3607_) as usize);
    v___x_3609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3609_, 0, v___x_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg___boxed(
    mut v_mvarId_3610_: *mut crate::leanh::LeanObject,
    mut v___y_3611_: *mut crate::leanh::LeanObject,
    mut v___y_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_3610_, v___y_3611_);
    crate::leanh::lean_dec(v___y_3611_);
    crate::leanh::lean_dec(v_mvarId_3610_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(
    mut v_x_3614_: *mut crate::leanh::LeanObject,
    mut v_x_3615_: *mut crate::leanh::LeanObject,
    mut v_x_3616_: *mut crate::leanh::LeanObject,
    mut v_x_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: u8 = 0;
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3618_ = crate::leanh::lean_ctor_get(v_x_3614_, 0);
                v_vs_3619_ = crate::leanh::lean_ctor_get(v_x_3614_, 1);
                v_isSharedCheck_3643_ = (!crate::leanh::lean_is_exclusive(v_x_3614_)) as u8;
                if v_isSharedCheck_3643_ == 0 {
                    v___x_3621_ = v_x_3614_;
                    v_isShared_3622_ = v_isSharedCheck_3643_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3619_);
                    crate::leanh::lean_inc(v_ks_3618_);
                    crate::leanh::lean_dec(v_x_3614_);
                    v___x_3621_ = crate::leanh::lean_box(0);
                    v_isShared_3622_ = v_isSharedCheck_3643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3623_ = lean_array_get_size(v_ks_3618_);
                v___x_3624_ = lean_nat_dec_lt(v_x_3615_, v___x_3623_);
                if v___x_3624_ == 0 {
                    crate::leanh::lean_dec(v_x_3615_);
                    v___x_3625_ = lean_array_push(v_ks_3618_, v_x_3616_);
                    v___x_3626_ = lean_array_push(v_vs_3619_, v_x_3617_);
                    if v_isShared_3622_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3621_, 1, v___x_3626_);
                        crate::leanh::lean_ctor_set(v___x_3621_, 0, v___x_3625_);
                        v___x_3628_ = v___x_3621_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3629_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3625_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___x_3626_);
                        v___x_3628_ = v_reuseFailAlloc_3629_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3630_ = lean_array_fget_borrowed(v_ks_3618_, v_x_3615_);
                    v___x_3631_ = l_Lean_instBEqMVarId_beq(v_x_3616_, v_k_x27_3630_);
                    if v___x_3631_ == 0 {
                        if v_isShared_3622_ == 0 {
                            v___x_3633_ = v___x_3621_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3637_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_ks_3618_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_vs_3619_);
                            v___x_3633_ = v_reuseFailAlloc_3637_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3638_ = lean_array_fset(v_ks_3618_, v_x_3615_, v_x_3616_);
                        v___x_3639_ = lean_array_fset(v_vs_3619_, v_x_3615_, v_x_3617_);
                        crate::leanh::lean_dec(v_x_3615_);
                        if v_isShared_3622_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3621_, 1, v___x_3639_);
                            crate::leanh::lean_ctor_set(v___x_3621_, 0, v___x_3638_);
                            v___x_3641_ = v___x_3621_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3642_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3638_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 1, v___x_3639_);
                            v___x_3641_ = v_reuseFailAlloc_3642_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3628_;
            }
            3 => {
                v___x_3634_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3635_ = lean_nat_add(v_x_3615_, v___x_3634_);
                crate::leanh::lean_dec(v_x_3615_);
                v_x_3614_ = v___x_3633_;
                v_x_3615_ = v___x_3635_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(
    mut v_n_3644_: *mut crate::leanh::LeanObject,
    mut v_k_3645_: *mut crate::leanh::LeanObject,
    mut v_v_3646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3647_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3648_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_n_3644_, v___x_3647_, v_k_3645_, v_v_3646_);
    return v___x_3648_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3649_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3649_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(
    mut v_x_3650_: *mut crate::leanh::LeanObject,
    mut v_x_3651_: usize,
    mut v_x_3652_: usize,
    mut v_x_3653_: *mut crate::leanh::LeanObject,
    mut v_x_3654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: usize = 0;
    let mut v___x_3657_: usize = 0;
    let mut v___x_3658_: usize = 0;
    let mut v___x_3659_: usize = 0;
    let mut v_j_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_v_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3679_: u8 = 0;
    let mut v___x_3680_: u8 = 0;
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_node_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3691_: usize = 0;
    let mut v___x_3692_: usize = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3697_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut v_unused_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3710_: u8 = 0;
    let mut v_ks_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: usize = 0;
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: u8 = 0;
    let mut v_reuseFailAlloc_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3650_) == 0 {
                    v_es_3655_ = crate::leanh::lean_ctor_get(v_x_3650_, 0);
                    v___x_3656_ = 5usize;
                    v___x_3657_ = 1usize;
                    v___x_3658_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_3659_ = lean_usize_land(v_x_3651_, v___x_3658_);
                    v_j_3660_ = lean_usize_to_nat(v___x_3659_);
                    v___x_3661_ = lean_array_get_size(v_es_3655_);
                    v___x_3662_ = lean_nat_dec_lt(v_j_3660_, v___x_3661_);
                    if v___x_3662_ == 0 {
                        crate::leanh::lean_dec(v_j_3660_);
                        crate::leanh::lean_dec(v_x_3654_);
                        crate::leanh::lean_dec(v_x_3653_);
                        return v_x_3650_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3655_);
                        v_isSharedCheck_3699_ = (!crate::leanh::lean_is_exclusive(v_x_3650_)) as u8;
                        if v_isSharedCheck_3699_ == 0 {
                            v_unused_3700_ = crate::leanh::lean_ctor_get(v_x_3650_, 0);
                            crate::leanh::lean_dec(v_unused_3700_);
                            v___x_3664_ = v_x_3650_;
                            v_isShared_3665_ = v_isSharedCheck_3699_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3650_);
                            v___x_3664_ = crate::leanh::lean_box(0);
                            v_isShared_3665_ = v_isSharedCheck_3699_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3701_ = crate::leanh::lean_ctor_get(v_x_3650_, 0);
                    v_vs_3702_ = crate::leanh::lean_ctor_get(v_x_3650_, 1);
                    v_isSharedCheck_3722_ = (!crate::leanh::lean_is_exclusive(v_x_3650_)) as u8;
                    if v_isSharedCheck_3722_ == 0 {
                        v___x_3704_ = v_x_3650_;
                        v_isShared_3705_ = v_isSharedCheck_3722_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3702_);
                        crate::leanh::lean_inc(v_ks_3701_);
                        crate::leanh::lean_dec(v_x_3650_);
                        v___x_3704_ = crate::leanh::lean_box(0);
                        v_isShared_3705_ = v_isSharedCheck_3722_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3666_ = lean_array_fget(v_es_3655_, v_j_3660_);
                v___x_3667_ = crate::leanh::lean_box(0);
                v_xs_x27_3668_ = lean_array_fset(v_es_3655_, v_j_3660_, v___x_3667_);
                match crate::leanh::lean_obj_tag(v_v_3666_) {
                    0 => {
                        v_key_3675_ = crate::leanh::lean_ctor_get(v_v_3666_, 0);
                        v_val_3676_ = crate::leanh::lean_ctor_get(v_v_3666_, 1);
                        v_isSharedCheck_3686_ = (!crate::leanh::lean_is_exclusive(v_v_3666_)) as u8;
                        if v_isSharedCheck_3686_ == 0 {
                            v___x_3678_ = v_v_3666_;
                            v_isShared_3679_ = v_isSharedCheck_3686_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3676_);
                            crate::leanh::lean_inc(v_key_3675_);
                            crate::leanh::lean_dec(v_v_3666_);
                            v___x_3678_ = crate::leanh::lean_box(0);
                            v_isShared_3679_ = v_isSharedCheck_3686_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3687_ = crate::leanh::lean_ctor_get(v_v_3666_, 0);
                        v_isSharedCheck_3697_ = (!crate::leanh::lean_is_exclusive(v_v_3666_)) as u8;
                        if v_isSharedCheck_3697_ == 0 {
                            v___x_3689_ = v_v_3666_;
                            v_isShared_3690_ = v_isSharedCheck_3697_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3687_);
                            crate::leanh::lean_dec(v_v_3666_);
                            v___x_3689_ = crate::leanh::lean_box(0);
                            v_isShared_3690_ = v_isSharedCheck_3697_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3698_, 0, v_x_3653_);
                        crate::leanh::lean_ctor_set(v___x_3698_, 1, v_x_3654_);
                        v___y_3670_ = v___x_3698_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3671_ = lean_array_fset(v_xs_x27_3668_, v_j_3660_, v___y_3670_);
                crate::leanh::lean_dec(v_j_3660_);
                if v_isShared_3665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3664_, 0, v___x_3671_);
                    v___x_3673_ = v___x_3664_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
                    v___x_3673_ = v_reuseFailAlloc_3674_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3673_;
            }
            4 => {
                v___x_3680_ = l_Lean_instBEqMVarId_beq(v_x_3653_, v_key_3675_);
                if v___x_3680_ == 0 {
                    crate::leanh::lean_del_object(v___x_3678_);
                    v___x_3681_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3675_,
                        v_val_3676_,
                        v_x_3653_,
                        v_x_3654_,
                    );
                    v___x_3682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3682_, 0, v___x_3681_);
                    v___y_3670_ = v___x_3682_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3676_);
                    crate::leanh::lean_dec(v_key_3675_);
                    if v_isShared_3679_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3678_, 1, v_x_3654_);
                        crate::leanh::lean_ctor_set(v___x_3678_, 0, v_x_3653_);
                        v___x_3684_ = v___x_3678_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_x_3653_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_x_3654_);
                        v___x_3684_ = v_reuseFailAlloc_3685_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3670_ = v___x_3684_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3691_ = lean_usize_shift_right(v_x_3651_, v___x_3656_);
                v___x_3692_ = lean_usize_add(v_x_3652_, v___x_3657_);
                v___x_3693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_node_3687_, v___x_3691_, v___x_3692_, v_x_3653_, v_x_3654_);
                if v_isShared_3690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v___x_3693_);
                    v___x_3695_ = v___x_3689_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
                    v___x_3695_ = v_reuseFailAlloc_3696_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3670_ = v___x_3695_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3705_ == 0 {
                    v___x_3707_ = v___x_3704_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3721_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_ks_3701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_vs_3702_);
                    v___x_3707_ = v_reuseFailAlloc_3721_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3708_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v___x_3707_, v_x_3653_, v_x_3654_);
                v___x_3716_ = 7usize;
                v___x_3717_ = lean_usize_dec_le(v___x_3716_, v_x_3652_);
                if v___x_3717_ == 0 {
                    v___x_3718_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3708_);
                    v___x_3719_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3720_ = lean_nat_dec_lt(v___x_3718_, v___x_3719_);
                    crate::leanh::lean_dec(v___x_3718_);
                    v___y_3710_ = v___x_3720_;
                    state = 10;
                    continue;
                } else {
                    v___y_3710_ = v___x_3717_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3710_ == 0 {
                    v_ks_3711_ = crate::leanh::lean_ctor_get(v_newNode_3708_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3711_);
                    v_vs_3712_ = crate::leanh::lean_ctor_get(v_newNode_3708_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3712_);
                    crate::leanh::lean_dec_ref(v_newNode_3708_);
                    v___x_3713_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3714_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0);
                    v___x_3715_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_x_3652_, v_ks_3711_, v_vs_3712_, v___x_3713_, v___x_3714_);
                    crate::leanh::lean_dec_ref(v_vs_3712_);
                    crate::leanh::lean_dec_ref(v_ks_3711_);
                    return v___x_3715_;
                } else {
                    return v_newNode_3708_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(
    mut v_depth_3723_: usize,
    mut v_keys_3724_: *mut crate::leanh::LeanObject,
    mut v_vals_3725_: *mut crate::leanh::LeanObject,
    mut v_i_3726_: *mut crate::leanh::LeanObject,
    mut v_entries_3727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: u8 = 0;
    let mut v_k_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: u64 = 0;
    let mut v_h_3733_: usize = 0;
    let mut v___x_3734_: usize = 0;
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: usize = 0;
    let mut v___x_3737_: usize = 0;
    let mut v___x_3738_: usize = 0;
    let mut v_h_3739_: usize = 0;
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3728_ = lean_array_get_size(v_keys_3724_);
                v___x_3729_ = lean_nat_dec_lt(v_i_3726_, v___x_3728_);
                if v___x_3729_ == 0 {
                    crate::leanh::lean_dec(v_i_3726_);
                    return v_entries_3727_;
                } else {
                    v_k_3730_ = lean_array_fget_borrowed(v_keys_3724_, v_i_3726_);
                    v_v_3731_ = lean_array_fget_borrowed(v_vals_3725_, v_i_3726_);
                    v___x_3732_ = l_Lean_instHashableMVarId_hash(v_k_3730_);
                    v_h_3733_ = lean_uint64_to_usize(v___x_3732_);
                    v___x_3734_ = 5usize;
                    v___x_3735_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3736_ = 1usize;
                    v___x_3737_ = lean_usize_sub(v_depth_3723_, v___x_3736_);
                    v___x_3738_ = lean_usize_mul(v___x_3734_, v___x_3737_);
                    v_h_3739_ = lean_usize_shift_right(v_h_3733_, v___x_3738_);
                    v___x_3740_ = lean_nat_add(v_i_3726_, v___x_3735_);
                    crate::leanh::lean_dec(v_i_3726_);
                    crate::leanh::lean_inc(v_v_3731_);
                    crate::leanh::lean_inc(v_k_3730_);
                    v___x_3741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_entries_3727_, v_h_3739_, v_depth_3723_, v_k_3730_, v_v_3731_);
                    v_i_3726_ = v___x_3740_;
                    v_entries_3727_ = v___x_3741_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(
    mut v_depth_3743_: *mut crate::leanh::LeanObject,
    mut v_keys_3744_: *mut crate::leanh::LeanObject,
    mut v_vals_3745_: *mut crate::leanh::LeanObject,
    mut v_i_3746_: *mut crate::leanh::LeanObject,
    mut v_entries_3747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3748_: usize = 0;
    let mut v_res_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3748_ = crate::leanh::lean_unbox_usize(v_depth_3743_);
    crate::leanh::lean_dec(v_depth_3743_);
    v_res_3749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_boxed_3748_, v_keys_3744_, v_vals_3745_, v_i_3746_, v_entries_3747_);
    crate::leanh::lean_dec_ref(v_vals_3745_);
    crate::leanh::lean_dec_ref(v_keys_3744_);
    return v_res_3749_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_x_3750_: *mut crate::leanh::LeanObject,
    mut v_x_3751_: *mut crate::leanh::LeanObject,
    mut v_x_3752_: *mut crate::leanh::LeanObject,
    mut v_x_3753_: *mut crate::leanh::LeanObject,
    mut v_x_3754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17747__boxed_3755_: usize = 0;
    let mut v_x_17748__boxed_3756_: usize = 0;
    let mut v_res_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17747__boxed_3755_ = crate::leanh::lean_unbox_usize(v_x_3751_);
    crate::leanh::lean_dec(v_x_3751_);
    v_x_17748__boxed_3756_ = crate::leanh::lean_unbox_usize(v_x_3752_);
    crate::leanh::lean_dec(v_x_3752_);
    v_res_3757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_3750_, v_x_17747__boxed_3755_, v_x_17748__boxed_3756_, v_x_3753_, v_x_3754_);
    return v_res_3757_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(
    mut v_x_3758_: *mut crate::leanh::LeanObject,
    mut v_x_3759_: *mut crate::leanh::LeanObject,
    mut v_x_3760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3761_: u64 = 0;
    let mut v___x_3762_: usize = 0;
    let mut v___x_3763_: usize = 0;
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3761_ = l_Lean_instHashableMVarId_hash(v_x_3759_);
    v___x_3762_ = lean_uint64_to_usize(v___x_3761_);
    v___x_3763_ = 1usize;
    v___x_3764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_3758_, v___x_3762_, v___x_3763_, v_x_3759_, v_x_3760_);
    return v___x_3764_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(
    mut v_mvarId_3765_: *mut crate::leanh::LeanObject,
    mut v_val_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v_depth_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3790_: u8 = 0;
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3769_ = lean_st_ref_take(v___y_3767_);
                v_mctx_3770_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                v_cache_3771_ = crate::leanh::lean_ctor_get(v___x_3769_, 1);
                v_zetaDeltaFVarIds_3772_ = crate::leanh::lean_ctor_get(v___x_3769_, 2);
                v_postponed_3773_ = crate::leanh::lean_ctor_get(v___x_3769_, 3);
                v_diag_3774_ = crate::leanh::lean_ctor_get(v___x_3769_, 4);
                v_isSharedCheck_3802_ = (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                if v_isSharedCheck_3802_ == 0 {
                    v___x_3776_ = v___x_3769_;
                    v_isShared_3777_ = v_isSharedCheck_3802_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3774_);
                    crate::leanh::lean_inc(v_postponed_3773_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3772_);
                    crate::leanh::lean_inc(v_cache_3771_);
                    crate::leanh::lean_inc(v_mctx_3770_);
                    crate::leanh::lean_dec(v___x_3769_);
                    v___x_3776_ = crate::leanh::lean_box(0);
                    v_isShared_3777_ = v_isSharedCheck_3802_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3778_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 0);
                v_levelAssignDepth_3779_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 1);
                v_lmvarCounter_3780_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 2);
                v_mvarCounter_3781_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 3);
                v_lDecls_3782_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 4);
                v_decls_3783_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 5);
                v_userNames_3784_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 6);
                v_lAssignment_3785_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 7);
                v_eAssignment_3786_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 8);
                v_dAssignment_3787_ = crate::leanh::lean_ctor_get(v_mctx_3770_, 9);
                v_isSharedCheck_3801_ = (!crate::leanh::lean_is_exclusive(v_mctx_3770_)) as u8;
                if v_isSharedCheck_3801_ == 0 {
                    v___x_3789_ = v_mctx_3770_;
                    v_isShared_3790_ = v_isSharedCheck_3801_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_3787_);
                    crate::leanh::lean_inc(v_eAssignment_3786_);
                    crate::leanh::lean_inc(v_lAssignment_3785_);
                    crate::leanh::lean_inc(v_userNames_3784_);
                    crate::leanh::lean_inc(v_decls_3783_);
                    crate::leanh::lean_inc(v_lDecls_3782_);
                    crate::leanh::lean_inc(v_mvarCounter_3781_);
                    crate::leanh::lean_inc(v_lmvarCounter_3780_);
                    crate::leanh::lean_inc(v_levelAssignDepth_3779_);
                    crate::leanh::lean_inc(v_depth_3778_);
                    crate::leanh::lean_dec(v_mctx_3770_);
                    v___x_3789_ = crate::leanh::lean_box(0);
                    v_isShared_3790_ = v_isSharedCheck_3801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3791_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_3786_, v_mvarId_3765_, v_val_3766_);
                if v_isShared_3790_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3789_, 8, v___x_3791_);
                    v___x_3793_ = v___x_3789_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3800_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_depth_3778_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3800_,
                        1,
                        v_levelAssignDepth_3779_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_lmvarCounter_3780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 3, v_mvarCounter_3781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 4, v_lDecls_3782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 5, v_decls_3783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 6, v_userNames_3784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 7, v_lAssignment_3785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 8, v___x_3791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 9, v_dAssignment_3787_);
                    v___x_3793_ = v_reuseFailAlloc_3800_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3777_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3776_, 0, v___x_3793_);
                    v___x_3795_ = v___x_3776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3799_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_cache_3771_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3799_,
                        2,
                        v_zetaDeltaFVarIds_3772_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_postponed_3773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 4, v_diag_3774_);
                    v___x_3795_ = v_reuseFailAlloc_3799_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3796_ = lean_st_ref_set(v___y_3767_, v___x_3795_);
                v___x_3797_ = crate::leanh::lean_box(0);
                v___x_3798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3798_, 0, v___x_3797_);
                return v___x_3798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg___boxed(
    mut v_mvarId_3803_: *mut crate::leanh::LeanObject,
    mut v_val_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_3803_, v_val_3804_, v___y_3805_);
    crate::leanh::lean_dec(v___y_3805_);
    return v_res_3807_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2() -> u64
{
    let mut v___x_3814_: u8 = 0;
    let mut v___x_3815_: u64 = 0;
    v___x_3814_ = 1;
    v___x_3815_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3814_);
    return v___x_3815_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(
    mut v___f_3816_: *mut crate::leanh::LeanObject,
    mut v_mv_3817_: *mut crate::leanh::LeanObject,
    mut v_val_3818_: *mut crate::leanh::LeanObject,
    mut v_tac_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
    mut v___y_3821_: *mut crate::leanh::LeanObject,
    mut v___y_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3841_: u8 = 0;
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v_a_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3865_: u8 = 0;
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3869_: u8 = 0;
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3885_: u8 = 0;
    let mut v_cancelTk_x3f_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3887_: u8 = 0;
    let mut v_inheritedTraceOptions_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3890_: u8 = 0;
    let mut v_ctxApprox_3891_: u8 = 0;
    let mut v_quasiPatternApprox_3892_: u8 = 0;
    let mut v_constApprox_3893_: u8 = 0;
    let mut v_isDefEqStuckEx_3894_: u8 = 0;
    let mut v_unificationHints_3895_: u8 = 0;
    let mut v_proofIrrelevance_3896_: u8 = 0;
    let mut v_assignSyntheticOpaque_3897_: u8 = 0;
    let mut v_offsetCnstrs_3898_: u8 = 0;
    let mut v_etaStruct_3899_: u8 = 0;
    let mut v_univApprox_3900_: u8 = 0;
    let mut v_iota_3901_: u8 = 0;
    let mut v_beta_3902_: u8 = 0;
    let mut v_proj_3903_: u8 = 0;
    let mut v_zeta_3904_: u8 = 0;
    let mut v_zetaDelta_3905_: u8 = 0;
    let mut v_zetaUnused_3906_: u8 = 0;
    let mut v_zetaHave_3907_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3910_: u8 = 0;
    let mut v_trackZetaDelta_3911_: u8 = 0;
    let mut v_zetaDeltaSet_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3918_: u8 = 0;
    let mut v_inTypeClassResolution_3919_: u8 = 0;
    let mut v_cacheInferType_3920_: u8 = 0;
    let mut v___x_3921_: u8 = 0;
    let mut v_config_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u64 = 0;
    let mut v___x_3925_: u64 = 0;
    let mut v___x_3926_: u64 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u64 = 0;
    let mut v___x_3931_: u64 = 0;
    let mut v_key_3932_: u64 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_reuseFailAlloc_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3827_ = crate::leanh::lean_box(0);
                v___x_3828_ = crate::leanh::lean_box(0);
                v___x_3829_ = 1;
                v___x_3833_ = crate::leanh::lean_box(1);
                v___x_3834_ = 0;
                v___x_3871_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3;
                v___x_3872_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
                crate::leanh::lean_ctor_set(v___x_3872_, 0, v___x_3827_);
                crate::leanh::lean_ctor_set(v___x_3872_, 1, v___x_3828_);
                crate::leanh::lean_ctor_set(v___x_3872_, 2, v___x_3827_);
                crate::leanh::lean_ctor_set(v___x_3872_, 3, v___f_3816_);
                crate::leanh::lean_ctor_set(v___x_3872_, 4, v___x_3833_);
                crate::leanh::lean_ctor_set(v___x_3872_, 5, v___x_3833_);
                crate::leanh::lean_ctor_set(v___x_3872_, 6, v___x_3827_);
                crate::leanh::lean_ctor_set(v___x_3872_, 7, v___x_3871_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    v___x_3829_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                    v___x_3829_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                    v___x_3829_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                    v___x_3829_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                    v___x_3834_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                    v___x_3834_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
                    v___x_3834_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                    v___x_3834_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                    v___x_3829_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                    v___x_3834_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                    v___x_3829_,
                );
                v_fileName_3873_ = crate::leanh::lean_ctor_get(v___y_3824_, 0);
                v_fileMap_3874_ = crate::leanh::lean_ctor_get(v___y_3824_, 1);
                v_options_3875_ = crate::leanh::lean_ctor_get(v___y_3824_, 2);
                v_currRecDepth_3876_ = crate::leanh::lean_ctor_get(v___y_3824_, 3);
                v_maxRecDepth_3877_ = crate::leanh::lean_ctor_get(v___y_3824_, 4);
                v_ref_3878_ = crate::leanh::lean_ctor_get(v___y_3824_, 5);
                v_currNamespace_3879_ = crate::leanh::lean_ctor_get(v___y_3824_, 6);
                v_openDecls_3880_ = crate::leanh::lean_ctor_get(v___y_3824_, 7);
                v_initHeartbeats_3881_ = crate::leanh::lean_ctor_get(v___y_3824_, 8);
                v_maxHeartbeats_3882_ = crate::leanh::lean_ctor_get(v___y_3824_, 9);
                v_quotContext_3883_ = crate::leanh::lean_ctor_get(v___y_3824_, 10);
                v_currMacroScope_3884_ = crate::leanh::lean_ctor_get(v___y_3824_, 11);
                v_diag_3885_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3824_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3886_ = crate::leanh::lean_ctor_get(v___y_3824_, 12);
                v_suppressElabErrors_3887_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3824_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3888_ = crate::leanh::lean_ctor_get(v___y_3824_, 13);
                v___x_3889_ = l_Lean_Meta_Context_config(v___y_3822_);
                v_foApprox_3890_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 0 as u32);
                v_ctxApprox_3891_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 1 as u32);
                v_quasiPatternApprox_3892_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_3889_, 2 as u32);
                v_constApprox_3893_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 3 as u32);
                v_isDefEqStuckEx_3894_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 4 as u32);
                v_unificationHints_3895_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 5 as u32);
                v_proofIrrelevance_3896_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 6 as u32);
                v_assignSyntheticOpaque_3897_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_3889_, 7 as u32);
                v_offsetCnstrs_3898_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 8 as u32);
                v_etaStruct_3899_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 10 as u32);
                v_univApprox_3900_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 11 as u32);
                v_iota_3901_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 12 as u32);
                v_beta_3902_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 13 as u32);
                v_proj_3903_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 14 as u32);
                v_zeta_3904_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 15 as u32);
                v_zetaDelta_3905_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 16 as u32);
                v_zetaUnused_3906_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 17 as u32);
                v_zetaHave_3907_ = crate::leanh::lean_ctor_get_uint8(v___x_3889_, 18 as u32);
                v_isSharedCheck_3945_ = (!crate::leanh::lean_is_exclusive(v___x_3889_)) as u8;
                if v_isSharedCheck_3945_ == 0 {
                    v___x_3909_ = v___x_3889_;
                    v_isShared_3910_ = v_isSharedCheck_3945_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3889_);
                    v___x_3909_ = crate::leanh::lean_box(0);
                    v_isShared_3910_ = v_isSharedCheck_3945_;
                    state = 9;
                    continue;
                }
            }
            1 => {
                v___x_3831_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0;
                v___x_3832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3832_, 0, v___x_3831_);
                return v___x_3832_;
            }
            2 => {
                v___x_3836_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mv_3817_, v___y_3823_);
                v_a_3837_ = crate::leanh::lean_ctor_get(v___x_3836_, 0);
                v_isSharedCheck_3870_ = (!crate::leanh::lean_is_exclusive(v___x_3836_)) as u8;
                if v_isSharedCheck_3870_ == 0 {
                    v___x_3839_ = v___x_3836_;
                    v_isShared_3840_ = v_isSharedCheck_3870_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3837_);
                    crate::leanh::lean_dec(v___x_3836_);
                    v___x_3839_ = crate::leanh::lean_box(0);
                    v_isShared_3840_ = v_isSharedCheck_3870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3841_ = (crate::leanh::lean_unbox(v_a_3837_) as u8);
                crate::leanh::lean_dec(v_a_3837_);
                if v___x_3841_ == 0 {
                    crate::leanh::lean_dec(v_mv_3817_);
                    v___x_3842_ =
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1;
                    if v_isShared_3840_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3839_, 0, v___x_3842_);
                        v___x_3844_ = v___x_3839_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
                        v___x_3844_ = v_reuseFailAlloc_3845_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3839_);
                    v___x_3846_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mv_3817_, v___y_3823_);
                    v_a_3847_ = crate::leanh::lean_ctor_get(v___x_3846_, 0);
                    crate::leanh::lean_inc(v_a_3847_);
                    crate::leanh::lean_dec_ref(v___x_3846_);
                    if crate::leanh::lean_obj_tag(v_a_3847_) == 1 {
                        v_val_3848_ = crate::leanh::lean_ctor_get(v_a_3847_, 0);
                        crate::leanh::lean_inc(v_val_3848_);
                        crate::leanh::lean_dec_ref_known(v_a_3847_, 1);
                        v___x_3849_ = l_Lean_Meta_Sym_unfoldReducible(
                            v_val_3848_,
                            v___y_3822_,
                            v___y_3823_,
                            v___y_3824_,
                            v___y_3825_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3849_) == 0 {
                            v_a_3850_ = crate::leanh::lean_ctor_get(v___x_3849_, 0);
                            crate::leanh::lean_inc(v_a_3850_);
                            crate::leanh::lean_dec_ref_known(v___x_3849_, 1);
                            v___x_3851_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_3850_, v___y_3821_);
                            if crate::leanh::lean_obj_tag(v___x_3851_) == 0 {
                                v_a_3852_ = crate::leanh::lean_ctor_get(v___x_3851_, 0);
                                crate::leanh::lean_inc(v_a_3852_);
                                crate::leanh::lean_dec_ref_known(v___x_3851_, 1);
                                v___x_3853_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mv_3817_, v_a_3852_, v___y_3823_);
                                crate::leanh::lean_dec_ref(v___x_3853_);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_mv_3817_);
                                v_a_3854_ = crate::leanh::lean_ctor_get(v___x_3851_, 0);
                                v_isSharedCheck_3861_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3851_)) as u8;
                                if v_isSharedCheck_3861_ == 0 {
                                    v___x_3856_ = v___x_3851_;
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3854_);
                                    crate::leanh::lean_dec(v___x_3851_);
                                    v___x_3856_ = crate::leanh::lean_box(0);
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_mv_3817_);
                            v_a_3862_ = crate::leanh::lean_ctor_get(v___x_3849_, 0);
                            v_isSharedCheck_3869_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3849_)) as u8;
                            if v_isSharedCheck_3869_ == 0 {
                                v___x_3864_ = v___x_3849_;
                                v_isShared_3865_ = v_isSharedCheck_3869_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3862_);
                                crate::leanh::lean_dec(v___x_3849_);
                                v___x_3864_ = crate::leanh::lean_box(0);
                                v_isShared_3865_ = v_isSharedCheck_3869_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3847_);
                        crate::leanh::lean_dec(v_mv_3817_);
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3844_;
            }
            5 => {
                if v_isShared_3857_ == 0 {
                    v___x_3859_ = v___x_3856_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3859_;
            }
            7 => {
                if v_isShared_3865_ == 0 {
                    v___x_3867_ = v___x_3864_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
                    v___x_3867_ = v_reuseFailAlloc_3868_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3867_;
            }
            9 => {
                v_trackZetaDelta_3911_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3912_ = crate::leanh::lean_ctor_get(v___y_3822_, 1);
                v_lctx_3913_ = crate::leanh::lean_ctor_get(v___y_3822_, 2);
                v_localInstances_3914_ = crate::leanh::lean_ctor_get(v___y_3822_, 3);
                v_defEqCtx_x3f_3915_ = crate::leanh::lean_ctor_get(v___y_3822_, 4);
                v_synthPendingDepth_3916_ = crate::leanh::lean_ctor_get(v___y_3822_, 5);
                v_canUnfold_x3f_3917_ = crate::leanh::lean_ctor_get(v___y_3822_, 6);
                v_univApprox_3918_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3919_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3920_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3921_ = 1;
                if v_isShared_3910_ == 0 {
                    v_config_3923_ = v___x_3909_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3944_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        0 as u32,
                        v_foApprox_3890_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        1 as u32,
                        v_ctxApprox_3891_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        2 as u32,
                        v_quasiPatternApprox_3892_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        3 as u32,
                        v_constApprox_3893_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        4 as u32,
                        v_isDefEqStuckEx_3894_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        5 as u32,
                        v_unificationHints_3895_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        6 as u32,
                        v_proofIrrelevance_3896_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        7 as u32,
                        v_assignSyntheticOpaque_3897_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        8 as u32,
                        v_offsetCnstrs_3898_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        10 as u32,
                        v_etaStruct_3899_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        11 as u32,
                        v_univApprox_3900_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        12 as u32,
                        v_iota_3901_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        13 as u32,
                        v_beta_3902_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        14 as u32,
                        v_proj_3903_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        15 as u32,
                        v_zeta_3904_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        16 as u32,
                        v_zetaDelta_3905_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        17 as u32,
                        v_zetaUnused_3906_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3944_,
                        18 as u32,
                        v_zetaHave_3907_,
                    );
                    v_config_3923_ = v_reuseFailAlloc_3944_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_ctor_set_uint8(v_config_3923_, 9 as u32, v___x_3921_);
                v___x_3924_ = l_Lean_Meta_Context_configKey(v___y_3822_);
                v___x_3925_ = 3u64;
                v___x_3926_ = lean_uint64_shift_right(v___x_3924_, v___x_3925_);
                v___x_3927_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5;
                v_ref_3928_ = l_Lean_replaceRef(v_val_3818_, v_ref_3878_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3888_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3886_);
                crate::leanh::lean_inc(v_currMacroScope_3884_);
                crate::leanh::lean_inc(v_quotContext_3883_);
                crate::leanh::lean_inc(v_maxHeartbeats_3882_);
                crate::leanh::lean_inc(v_initHeartbeats_3881_);
                crate::leanh::lean_inc(v_openDecls_3880_);
                crate::leanh::lean_inc(v_currNamespace_3879_);
                crate::leanh::lean_inc(v_maxRecDepth_3877_);
                crate::leanh::lean_inc(v_currRecDepth_3876_);
                crate::leanh::lean_inc_ref(v_options_3875_);
                crate::leanh::lean_inc_ref(v_fileMap_3874_);
                crate::leanh::lean_inc_ref(v_fileName_3873_);
                v___x_3929_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3929_, 0, v_fileName_3873_);
                crate::leanh::lean_ctor_set(v___x_3929_, 1, v_fileMap_3874_);
                crate::leanh::lean_ctor_set(v___x_3929_, 2, v_options_3875_);
                crate::leanh::lean_ctor_set(v___x_3929_, 3, v_currRecDepth_3876_);
                crate::leanh::lean_ctor_set(v___x_3929_, 4, v_maxRecDepth_3877_);
                crate::leanh::lean_ctor_set(v___x_3929_, 5, v_ref_3928_);
                crate::leanh::lean_ctor_set(v___x_3929_, 6, v_currNamespace_3879_);
                crate::leanh::lean_ctor_set(v___x_3929_, 7, v_openDecls_3880_);
                crate::leanh::lean_ctor_set(v___x_3929_, 8, v_initHeartbeats_3881_);
                crate::leanh::lean_ctor_set(v___x_3929_, 9, v_maxHeartbeats_3882_);
                crate::leanh::lean_ctor_set(v___x_3929_, 10, v_quotContext_3883_);
                crate::leanh::lean_ctor_set(v___x_3929_, 11, v_currMacroScope_3884_);
                crate::leanh::lean_ctor_set(v___x_3929_, 12, v_cancelTk_x3f_3886_);
                crate::leanh::lean_ctor_set(v___x_3929_, 13, v_inheritedTraceOptions_3888_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3929_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3885_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3929_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3887_,
                );
                v___x_3930_ = lean_uint64_shift_left(v___x_3926_, v___x_3925_);
                v___x_3931_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2);
                v_key_3932_ = lean_uint64_lor(v___x_3930_, v___x_3931_);
                v___x_3933_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_3933_, 0, v_config_3923_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_3933_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_3932_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_3917_);
                crate::leanh::lean_inc(v_synthPendingDepth_3916_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_3915_);
                crate::leanh::lean_inc_ref(v_localInstances_3914_);
                crate::leanh::lean_inc_ref(v_lctx_3913_);
                crate::leanh::lean_inc(v_zetaDeltaSet_3912_);
                v___x_3934_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_3934_, 0, v___x_3933_);
                crate::leanh::lean_ctor_set(v___x_3934_, 1, v_zetaDeltaSet_3912_);
                crate::leanh::lean_ctor_set(v___x_3934_, 2, v_lctx_3913_);
                crate::leanh::lean_ctor_set(v___x_3934_, 3, v_localInstances_3914_);
                crate::leanh::lean_ctor_set(v___x_3934_, 4, v_defEqCtx_x3f_3915_);
                crate::leanh::lean_ctor_set(v___x_3934_, 5, v_synthPendingDepth_3916_);
                crate::leanh::lean_ctor_set(v___x_3934_, 6, v_canUnfold_x3f_3917_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3911_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3918_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3919_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3920_,
                );
                crate::leanh::lean_inc(v_mv_3817_);
                v___x_3935_ = l_Lean_Elab_runTactic(
                    v_mv_3817_,
                    v_tac_3819_,
                    v___x_3872_,
                    v___x_3927_,
                    v___x_3934_,
                    v___y_3823_,
                    v___x_3929_,
                    v___y_3825_,
                );
                crate::leanh::lean_dec_ref_known(v___x_3929_, 14);
                crate::leanh::lean_dec_ref_known(v___x_3934_, 7);
                if crate::leanh::lean_obj_tag(v___x_3935_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3935_, 1);
                    state = 2;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3935_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3935_, 1);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_mv_3817_);
                        v_a_3936_ = crate::leanh::lean_ctor_get(v___x_3935_, 0);
                        v_isSharedCheck_3943_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3935_)) as u8;
                        if v_isSharedCheck_3943_ == 0 {
                            v___x_3938_ = v___x_3935_;
                            v_isShared_3939_ = v_isSharedCheck_3943_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3936_);
                            crate::leanh::lean_dec(v___x_3935_);
                            v___x_3938_ = crate::leanh::lean_box(0);
                            v_isShared_3939_ = v_isSharedCheck_3943_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            11 => {
                if v_isShared_3939_ == 0 {
                    v___x_3941_ = v___x_3938_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___boxed(
    mut v___f_3946_: *mut crate::leanh::LeanObject,
    mut v_mv_3947_: *mut crate::leanh::LeanObject,
    mut v_val_3948_: *mut crate::leanh::LeanObject,
    mut v_tac_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(
        v___f_3946_,
        v_mv_3947_,
        v_val_3948_,
        v_tac_3949_,
        v___y_3950_,
        v___y_3951_,
        v___y_3952_,
        v___y_3953_,
        v___y_3954_,
        v___y_3955_,
    );
    crate::leanh::lean_dec(v___y_3955_);
    crate::leanh::lean_dec_ref(v___y_3954_);
    crate::leanh::lean_dec(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    crate::leanh::lean_dec(v___y_3951_);
    crate::leanh::lean_dec_ref(v___y_3950_);
    crate::leanh::lean_dec(v_val_3948_);
    return v_res_3957_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(
    mut v_a_3958_: *mut crate::leanh::LeanObject,
    mut v_x_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3959_) == 0 {
                    v___x_3960_ = crate::leanh::lean_box(0);
                    return v___x_3960_;
                } else {
                    v_key_3961_ = crate::leanh::lean_ctor_get(v_x_3959_, 0);
                    v_value_3962_ = crate::leanh::lean_ctor_get(v_x_3959_, 1);
                    v_tail_3963_ = crate::leanh::lean_ctor_get(v_x_3959_, 2);
                    v___x_3964_ = lean_nat_dec_eq(v_key_3961_, v_a_3958_);
                    if v___x_3964_ == 0 {
                        v_x_3959_ = v_tail_3963_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3962_);
                        v___x_3966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3966_, 0, v_value_3962_);
                        return v___x_3966_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_x_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_3967_, v_x_3968_);
    crate::leanh::lean_dec(v_x_3968_);
    crate::leanh::lean_dec(v_a_3967_);
    return v_res_3969_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(
    mut v_m_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u64 = 0;
    let mut v___x_3975_: u64 = 0;
    let mut v___x_3976_: u64 = 0;
    let mut v_fold_3977_: u64 = 0;
    let mut v___x_3978_: u64 = 0;
    let mut v___x_3979_: u64 = 0;
    let mut v___x_3980_: u64 = 0;
    let mut v___x_3981_: usize = 0;
    let mut v___x_3982_: usize = 0;
    let mut v___x_3983_: usize = 0;
    let mut v___x_3984_: usize = 0;
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3972_ = crate::leanh::lean_ctor_get(v_m_3970_, 1);
    v___x_3973_ = lean_array_get_size(v_buckets_3972_);
    v___x_3974_ = lean_uint64_of_nat(v_a_3971_);
    v___x_3975_ = 32u64;
    v___x_3976_ = lean_uint64_shift_right(v___x_3974_, v___x_3975_);
    v_fold_3977_ = lean_uint64_xor(v___x_3974_, v___x_3976_);
    v___x_3978_ = 16u64;
    v___x_3979_ = lean_uint64_shift_right(v_fold_3977_, v___x_3978_);
    v___x_3980_ = lean_uint64_xor(v_fold_3977_, v___x_3979_);
    v___x_3981_ = lean_uint64_to_usize(v___x_3980_);
    v___x_3982_ = lean_usize_of_nat(v___x_3973_);
    v___x_3983_ = 1usize;
    v___x_3984_ = lean_usize_sub(v___x_3982_, v___x_3983_);
    v___x_3985_ = lean_usize_land(v___x_3981_, v___x_3984_);
    v___x_3986_ = lean_array_uget_borrowed(v_buckets_3972_, v___x_3985_);
    v___x_3987_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_3971_, v___x_3986_);
    return v___x_3987_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg___boxed(
    mut v_m_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_3988_, v_a_3989_);
    crate::leanh::lean_dec(v_a_3989_);
    crate::leanh::lean_dec_ref(v_m_3988_);
    return v_res_3990_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4040_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_4040_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(
    mut v_invariantAlts_4053_: *mut crate::leanh::LeanObject,
    mut v_n_4054_: *mut crate::leanh::LeanObject,
    mut v_mv_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
    mut v_a_4059_: *mut crate::leanh::LeanObject,
    mut v_a_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4065_: u8 = 0;
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4074_: u8 = 0;
    let mut v_a_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4079_: u8 = 0;
    let mut v_a_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: u8 = 0;
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4087_: u8 = 0;
    let mut v___f_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: u8 = 0;
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4155_: u8 = 0;
    let mut v___x_4156_: u8 = 0;
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_4053_, v_n_4054_);
                if crate::leanh::lean_obj_tag(v___x_4083_) == 1 {
                    v_val_4084_ = crate::leanh::lean_ctor_get(v___x_4083_, 0);
                    v_isSharedCheck_4155_ = (!crate::leanh::lean_is_exclusive(v___x_4083_)) as u8;
                    if v_isSharedCheck_4155_ == 0 {
                        v___x_4086_ = v___x_4083_;
                        v_isShared_4087_ = v_isSharedCheck_4155_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4084_);
                        crate::leanh::lean_dec(v___x_4083_);
                        v___x_4086_ = crate::leanh::lean_box(0);
                        v_isShared_4087_ = v_isSharedCheck_4155_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4083_);
                    crate::leanh::lean_dec(v_mv_4055_);
                    v___x_4156_ = 0;
                    v___x_4157_ = crate::leanh::lean_box((v___x_4156_) as usize);
                    v___x_4158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4158_, 0, v___x_4157_);
                    return v___x_4158_;
                }
            }
            1 => {
                if v___y_4065_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4064_);
                    v___x_4066_ = crate::leanh::lean_box((v___y_4065_) as usize);
                    v___x_4067_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4067_, 0, v___x_4066_);
                    return v___x_4067_;
                } else {
                    v___x_4068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4068_, 0, v___y_4064_);
                    return v___x_4068_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4070_) == 0 {
                    v_a_4071_ = crate::leanh::lean_ctor_get(v___y_4070_, 0);
                    v_isSharedCheck_4079_ = (!crate::leanh::lean_is_exclusive(v___y_4070_)) as u8;
                    if v_isSharedCheck_4079_ == 0 {
                        v___x_4073_ = v___y_4070_;
                        v_isShared_4074_ = v_isSharedCheck_4079_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4071_);
                        crate::leanh::lean_dec(v___y_4070_);
                        v___x_4073_ = crate::leanh::lean_box(0);
                        v_isShared_4074_ = v_isSharedCheck_4079_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4080_ = crate::leanh::lean_ctor_get(v___y_4070_, 0);
                    crate::leanh::lean_inc(v_a_4080_);
                    crate::leanh::lean_dec_ref_known(v___y_4070_, 1);
                    v___x_4081_ = l_Lean_Exception_isInterrupt(v_a_4080_);
                    if v___x_4081_ == 0 {
                        crate::leanh::lean_inc(v_a_4080_);
                        v___x_4082_ = l_Lean_Exception_isRuntime(v_a_4080_);
                        v___y_4064_ = v_a_4080_;
                        v___y_4065_ = v___x_4082_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4064_ = v_a_4080_;
                        v___y_4065_ = v___x_4081_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v_a_4075_ = crate::leanh::lean_ctor_get(v_a_4071_, 0);
                crate::leanh::lean_inc(v_a_4075_);
                crate::leanh::lean_dec(v_a_4071_);
                if v_isShared_4074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4073_, 0, v_a_4075_);
                    v___x_4077_ = v___x_4073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4075_);
                    v___x_4077_ = v_reuseFailAlloc_4078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4077_;
            }
            5 => {
                v___f_4088_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2;
                v___x_4089_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3;
                crate::leanh::lean_inc(v_val_4084_);
                v___x_4090_ = l_Lean_Syntax_isOfKind(v_val_4084_, v___x_4089_);
                if v___x_4090_ == 0 {
                    v___x_4091_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5;
                    crate::leanh::lean_inc(v_val_4084_);
                    v___x_4092_ = l_Lean_Syntax_isOfKind(v_val_4084_, v___x_4091_);
                    if v___x_4092_ == 0 {
                        crate::leanh::lean_dec(v_val_4084_);
                        crate::leanh::lean_dec(v_mv_4055_);
                        v___x_4093_ = crate::leanh::lean_box((v___x_4092_) as usize);
                        if v_isShared_4087_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4086_, 0);
                            crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4093_);
                            v___x_4095_ = v___x_4086_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4096_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
                            v___x_4095_ = v_reuseFailAlloc_4096_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_4097_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4098_ = l_Lean_Syntax_getArg(v_val_4084_, v___x_4097_);
                        v___x_4099_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7;
                        crate::leanh::lean_inc(v___x_4098_);
                        v___x_4100_ = l_Lean_Syntax_isOfKind(v___x_4098_, v___x_4099_);
                        if v___x_4100_ == 0 {
                            crate::leanh::lean_dec(v___x_4098_);
                            crate::leanh::lean_dec(v_val_4084_);
                            crate::leanh::lean_dec(v_mv_4055_);
                            v___x_4101_ = crate::leanh::lean_box((v___x_4100_) as usize);
                            if v_isShared_4087_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4086_, 0);
                                crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4101_);
                                v___x_4103_ = v___x_4086_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_4104_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4101_);
                                v___x_4103_ = v_reuseFailAlloc_4104_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4086_);
                            v_ref_4105_ = crate::leanh::lean_ctor_get(v_a_4060_, 5);
                            v___x_4106_ = l_Lean_Syntax_getArg(v___x_4098_, v___x_4097_);
                            crate::leanh::lean_dec(v___x_4098_);
                            v___x_4107_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4108_ = l_Lean_Syntax_getArg(v_val_4084_, v___x_4107_);
                            v_args_4109_ = l_Lean_Syntax_getArgs(v___x_4106_);
                            crate::leanh::lean_dec(v___x_4106_);
                            v___x_4110_ = l_Lean_SourceInfo_fromRef(v_ref_4105_, v___x_4090_);
                            v___x_4111_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9;
                            v___x_4112_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10;
                            crate::leanh::lean_inc_n(v___x_4110_, 11);
                            v___x_4113_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4113_, 0, v___x_4110_);
                            crate::leanh::lean_ctor_set(v___x_4113_, 1, v___x_4112_);
                            v___x_4114_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12;
                            v___x_4115_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14;
                            v___x_4116_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16;
                            v___x_4117_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18;
                            v___x_4118_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19;
                            v___x_4119_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4119_, 0, v___x_4110_);
                            crate::leanh::lean_ctor_set(v___x_4119_, 1, v___x_4118_);
                            v___x_4120_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20);
                            v___x_4121_ = l_Array_append___redArg(v___x_4120_, v_args_4109_);
                            crate::leanh::lean_dec_ref(v_args_4109_);
                            v___x_4122_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4122_, 0, v___x_4110_);
                            crate::leanh::lean_ctor_set(v___x_4122_, 1, v___x_4116_);
                            crate::leanh::lean_ctor_set(v___x_4122_, 2, v___x_4121_);
                            v___x_4123_ = l_Lean_Syntax_node2(
                                v___x_4110_,
                                v___x_4117_,
                                v___x_4119_,
                                v___x_4122_,
                            );
                            v___x_4124_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21;
                            v___x_4125_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4125_, 0, v___x_4110_);
                            crate::leanh::lean_ctor_set(v___x_4125_, 1, v___x_4124_);
                            v___x_4126_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22;
                            v___x_4127_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23;
                            v___x_4128_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4128_, 0, v___x_4110_);
                            crate::leanh::lean_ctor_set(v___x_4128_, 1, v___x_4126_);
                            v___x_4129_ = l_Lean_Syntax_node2(
                                v___x_4110_,
                                v___x_4127_,
                                v___x_4128_,
                                v___x_4108_,
                            );
                            v___x_4130_ = l_Lean_Syntax_node3(
                                v___x_4110_,
                                v___x_4116_,
                                v___x_4123_,
                                v___x_4125_,
                                v___x_4129_,
                            );
                            v___x_4131_ =
                                l_Lean_Syntax_node1(v___x_4110_, v___x_4115_, v___x_4130_);
                            v___x_4132_ =
                                l_Lean_Syntax_node1(v___x_4110_, v___x_4114_, v___x_4131_);
                            v___x_4133_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24;
                            v___x_4134_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4110_);
                            crate::leanh::lean_ctor_set(v___x_4134_, 1, v___x_4133_);
                            v___x_4135_ = l_Lean_Syntax_node3(
                                v___x_4110_,
                                v___x_4111_,
                                v___x_4113_,
                                v___x_4132_,
                                v___x_4134_,
                            );
                            v___x_4136_ =
                                l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(
                                    v___f_4088_,
                                    v_mv_4055_,
                                    v_val_4084_,
                                    v___x_4135_,
                                    v_a_4056_,
                                    v_a_4057_,
                                    v_a_4058_,
                                    v_a_4059_,
                                    v_a_4060_,
                                    v_a_4061_,
                                );
                            crate::leanh::lean_dec(v_val_4084_);
                            v___y_4070_ = v___x_4136_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_4137_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4138_ = l_Lean_Syntax_getArg(v_val_4084_, v___x_4137_);
                    v___x_4139_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26;
                    v___x_4140_ = l_Lean_Syntax_isOfKind(v___x_4138_, v___x_4139_);
                    if v___x_4140_ == 0 {
                        crate::leanh::lean_dec(v_val_4084_);
                        crate::leanh::lean_dec(v_mv_4055_);
                        v___x_4141_ = crate::leanh::lean_box((v___x_4140_) as usize);
                        if v_isShared_4087_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4086_, 0);
                            crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4141_);
                            v___x_4143_ = v___x_4086_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4144_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
                            v___x_4143_ = v_reuseFailAlloc_4144_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4086_);
                        v_ref_4145_ = crate::leanh::lean_ctor_get(v_a_4060_, 5);
                        v___x_4146_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4147_ = l_Lean_Syntax_getArg(v_val_4084_, v___x_4146_);
                        v___x_4148_ = 0;
                        v___x_4149_ = l_Lean_SourceInfo_fromRef(v_ref_4145_, v___x_4148_);
                        v___x_4150_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22;
                        v___x_4151_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23;
                        crate::leanh::lean_inc(v___x_4149_);
                        v___x_4152_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4152_, 0, v___x_4149_);
                        crate::leanh::lean_ctor_set(v___x_4152_, 1, v___x_4150_);
                        v___x_4153_ =
                            l_Lean_Syntax_node2(v___x_4149_, v___x_4151_, v___x_4152_, v___x_4147_);
                        v___x_4154_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(
                            v___f_4088_,
                            v_mv_4055_,
                            v_val_4084_,
                            v___x_4153_,
                            v_a_4056_,
                            v_a_4057_,
                            v_a_4058_,
                            v_a_4059_,
                            v_a_4060_,
                            v_a_4061_,
                        );
                        crate::leanh::lean_dec(v_val_4084_);
                        v___y_4070_ = v___x_4154_;
                        state = 2;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4095_;
            }
            7 => {
                return v___x_4103_;
            }
            8 => {
                return v___x_4143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___boxed(
    mut v_invariantAlts_4159_: *mut crate::leanh::LeanObject,
    mut v_n_4160_: *mut crate::leanh::LeanObject,
    mut v_mv_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(
        v_invariantAlts_4159_,
        v_n_4160_,
        v_mv_4161_,
        v_a_4162_,
        v_a_4163_,
        v_a_4164_,
        v_a_4165_,
        v_a_4166_,
        v_a_4167_,
    );
    crate::leanh::lean_dec(v_a_4167_);
    crate::leanh::lean_dec_ref(v_a_4166_);
    crate::leanh::lean_dec(v_a_4165_);
    crate::leanh::lean_dec_ref(v_a_4164_);
    crate::leanh::lean_dec(v_a_4163_);
    crate::leanh::lean_dec_ref(v_a_4162_);
    crate::leanh::lean_dec(v_n_4160_);
    crate::leanh::lean_dec_ref(v_invariantAlts_4159_);
    return v_res_4169_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(
    mut v_00_u03b2_4170_: *mut crate::leanh::LeanObject,
    mut v_m_4171_: *mut crate::leanh::LeanObject,
    mut v_a_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_4171_, v_a_4172_);
    return v___x_4173_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___boxed(
    mut v_00_u03b2_4174_: *mut crate::leanh::LeanObject,
    mut v_m_4175_: *mut crate::leanh::LeanObject,
    mut v_a_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(v_00_u03b2_4174_, v_m_4175_, v_a_4176_);
    crate::leanh::lean_dec(v_a_4176_);
    crate::leanh::lean_dec_ref(v_m_4175_);
    return v_res_4177_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(
    mut v_mvarId_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4186_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_4178_, v___y_4182_);
    return v___x_4186_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___boxed(
    mut v_mvarId_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4195_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(
            v_mvarId_4187_,
            v___y_4188_,
            v___y_4189_,
            v___y_4190_,
            v___y_4191_,
            v___y_4192_,
            v___y_4193_,
        );
    crate::leanh::lean_dec(v___y_4193_);
    crate::leanh::lean_dec_ref(v___y_4192_);
    crate::leanh::lean_dec(v___y_4191_);
    crate::leanh::lean_dec_ref(v___y_4190_);
    crate::leanh::lean_dec(v___y_4189_);
    crate::leanh::lean_dec_ref(v___y_4188_);
    crate::leanh::lean_dec(v_mvarId_4187_);
    return v_res_4195_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(
    mut v_mvarId_4196_: *mut crate::leanh::LeanObject,
    mut v_val_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4205_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_4196_, v_val_4197_, v___y_4201_);
    return v___x_4205_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___boxed(
    mut v_mvarId_4206_: *mut crate::leanh::LeanObject,
    mut v_val_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
    mut v___y_4210_: *mut crate::leanh::LeanObject,
    mut v___y_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
    mut v___y_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4215_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(
            v_mvarId_4206_,
            v_val_4207_,
            v___y_4208_,
            v___y_4209_,
            v___y_4210_,
            v___y_4211_,
            v___y_4212_,
            v___y_4213_,
        );
    crate::leanh::lean_dec(v___y_4213_);
    crate::leanh::lean_dec_ref(v___y_4212_);
    crate::leanh::lean_dec(v___y_4211_);
    crate::leanh::lean_dec_ref(v___y_4210_);
    crate::leanh::lean_dec(v___y_4209_);
    crate::leanh::lean_dec_ref(v___y_4208_);
    return v_res_4215_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(
    mut v_00_u03b2_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_x_4218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_4217_, v_x_4218_);
    return v___x_4219_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___boxed(
    mut v_00_u03b2_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_x_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4223_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_4220_, v_a_4221_, v_x_4222_);
    crate::leanh::lean_dec(v_x_4222_);
    crate::leanh::lean_dec(v_a_4221_);
    return v_res_4223_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(
    mut v_00_u03b2_4224_: *mut crate::leanh::LeanObject,
    mut v_x_4225_: *mut crate::leanh::LeanObject,
    mut v_x_4226_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4227_: u8 = 0;
    v___x_4227_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_4225_, v_x_4226_);
    return v___x_4227_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___boxed(
    mut v_00_u03b2_4228_: *mut crate::leanh::LeanObject,
    mut v_x_4229_: *mut crate::leanh::LeanObject,
    mut v_x_4230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4231_: u8 = 0;
    let mut v_r_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4231_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_4228_, v_x_4229_, v_x_4230_);
    crate::leanh::lean_dec(v_x_4230_);
    crate::leanh::lean_dec_ref(v_x_4229_);
    v_r_4232_ = crate::leanh::lean_box((v_res_4231_) as usize);
    return v_r_4232_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5(
    mut v_00_u03b2_4233_: *mut crate::leanh::LeanObject,
    mut v_x_4234_: *mut crate::leanh::LeanObject,
    mut v_x_4235_: *mut crate::leanh::LeanObject,
    mut v_x_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4237_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_4234_, v_x_4235_, v_x_4236_);
    return v___x_4237_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4238_: *mut crate::leanh::LeanObject,
    mut v_x_4239_: *mut crate::leanh::LeanObject,
    mut v_x_4240_: usize,
    mut v_x_4241_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4242_: u8 = 0;
    v___x_4242_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_4239_, v_x_4240_, v_x_4241_);
    return v___x_4242_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_4243_: *mut crate::leanh::LeanObject,
    mut v_x_4244_: *mut crate::leanh::LeanObject,
    mut v_x_4245_: *mut crate::leanh::LeanObject,
    mut v_x_4246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18672__boxed_4247_: usize = 0;
    let mut v_res_4248_: u8 = 0;
    let mut v_r_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18672__boxed_4247_ = crate::leanh::lean_unbox_usize(v_x_4245_);
    crate::leanh::lean_dec(v_x_4245_);
    v_res_4248_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_4243_, v_x_4244_, v_x_18672__boxed_4247_, v_x_4246_);
    crate::leanh::lean_dec(v_x_4246_);
    crate::leanh::lean_dec_ref(v_x_4244_);
    v_r_4249_ = crate::leanh::lean_box((v_res_4248_) as usize);
    return v_r_4249_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(
    mut v_00_u03b2_4250_: *mut crate::leanh::LeanObject,
    mut v_x_4251_: *mut crate::leanh::LeanObject,
    mut v_x_4252_: usize,
    mut v_x_4253_: usize,
    mut v_x_4254_: *mut crate::leanh::LeanObject,
    mut v_x_4255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_4251_, v_x_4252_, v_x_4253_, v_x_4254_, v_x_4255_);
    return v___x_4256_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b2_4257_: *mut crate::leanh::LeanObject,
    mut v_x_4258_: *mut crate::leanh::LeanObject,
    mut v_x_4259_: *mut crate::leanh::LeanObject,
    mut v_x_4260_: *mut crate::leanh::LeanObject,
    mut v_x_4261_: *mut crate::leanh::LeanObject,
    mut v_x_4262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18683__boxed_4263_: usize = 0;
    let mut v_x_18684__boxed_4264_: usize = 0;
    let mut v_res_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18683__boxed_4263_ = crate::leanh::lean_unbox_usize(v_x_4259_);
    crate::leanh::lean_dec(v_x_4259_);
    v_x_18684__boxed_4264_ = crate::leanh::lean_unbox_usize(v_x_4260_);
    crate::leanh::lean_dec(v_x_4260_);
    v_res_4265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_4257_, v_x_4258_, v_x_18683__boxed_4263_, v_x_18684__boxed_4264_, v_x_4261_, v_x_4262_);
    return v_res_4265_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_4266_: *mut crate::leanh::LeanObject,
    mut v_keys_4267_: *mut crate::leanh::LeanObject,
    mut v_vals_4268_: *mut crate::leanh::LeanObject,
    mut v_heq_4269_: *mut crate::leanh::LeanObject,
    mut v_i_4270_: *mut crate::leanh::LeanObject,
    mut v_k_4271_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4272_: u8 = 0;
    v___x_4272_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_4267_, v_i_4270_, v_k_4271_);
    return v___x_4272_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_4273_: *mut crate::leanh::LeanObject,
    mut v_keys_4274_: *mut crate::leanh::LeanObject,
    mut v_vals_4275_: *mut crate::leanh::LeanObject,
    mut v_heq_4276_: *mut crate::leanh::LeanObject,
    mut v_i_4277_: *mut crate::leanh::LeanObject,
    mut v_k_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4279_: u8 = 0;
    let mut v_r_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4273_, v_keys_4274_, v_vals_4275_, v_heq_4276_, v_i_4277_, v_k_4278_);
    crate::leanh::lean_dec(v_k_4278_);
    crate::leanh::lean_dec_ref(v_vals_4275_);
    crate::leanh::lean_dec_ref(v_keys_4274_);
    v_r_4280_ = crate::leanh::lean_box((v_res_4279_) as usize);
    return v_r_4280_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(
    mut v_00_u03b2_4281_: *mut crate::leanh::LeanObject,
    mut v_n_4282_: *mut crate::leanh::LeanObject,
    mut v_k_4283_: *mut crate::leanh::LeanObject,
    mut v_v_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_4282_, v_k_4283_, v_v_4284_);
    return v___x_4285_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(
    mut v_00_u03b2_4286_: *mut crate::leanh::LeanObject,
    mut v_depth_4287_: usize,
    mut v_keys_4288_: *mut crate::leanh::LeanObject,
    mut v_vals_4289_: *mut crate::leanh::LeanObject,
    mut v_heq_4290_: *mut crate::leanh::LeanObject,
    mut v_i_4291_: *mut crate::leanh::LeanObject,
    mut v_entries_4292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_4287_, v_keys_4288_, v_vals_4289_, v_i_4291_, v_entries_4292_);
    return v___x_4293_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(
    mut v_00_u03b2_4294_: *mut crate::leanh::LeanObject,
    mut v_depth_4295_: *mut crate::leanh::LeanObject,
    mut v_keys_4296_: *mut crate::leanh::LeanObject,
    mut v_vals_4297_: *mut crate::leanh::LeanObject,
    mut v_heq_4298_: *mut crate::leanh::LeanObject,
    mut v_i_4299_: *mut crate::leanh::LeanObject,
    mut v_entries_4300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4301_: usize = 0;
    let mut v_res_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4301_ = crate::leanh::lean_unbox_usize(v_depth_4295_);
    crate::leanh::lean_dec(v_depth_4295_);
    v_res_4302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_4294_, v_depth_boxed_4301_, v_keys_4296_, v_vals_4297_, v_heq_4298_, v_i_4299_, v_entries_4300_);
    crate::leanh::lean_dec_ref(v_vals_4297_);
    crate::leanh::lean_dec_ref(v_keys_4296_);
    return v_res_4302_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(
    mut v_00_u03b2_4303_: *mut crate::leanh::LeanObject,
    mut v_x_4304_: *mut crate::leanh::LeanObject,
    mut v_x_4305_: *mut crate::leanh::LeanObject,
    mut v_x_4306_: *mut crate::leanh::LeanObject,
    mut v_x_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_4304_, v_x_4305_, v_x_4306_, v_x_4307_);
    return v___x_4308_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_x_4310_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4311_: u8 = 0;
    let mut v_key_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4310_) == 0 {
                    v___x_4311_ = 0;
                    return v___x_4311_;
                } else {
                    v_key_4312_ = crate::leanh::lean_ctor_get(v_x_4310_, 0);
                    v_tail_4313_ = crate::leanh::lean_ctor_get(v_x_4310_, 2);
                    v___x_4314_ = lean_nat_dec_eq(v_key_4312_, v_a_4309_);
                    if v___x_4314_ == 0 {
                        v_x_4310_ = v_tail_4313_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4314_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_x_4317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4318_: u8 = 0;
    let mut v_r_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_4316_, v_x_4317_);
    crate::leanh::lean_dec(v_x_4317_);
    crate::leanh::lean_dec(v_a_4316_);
    v_r_4319_ = crate::leanh::lean_box((v_res_4318_) as usize);
    return v_r_4319_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_4320_: *mut crate::leanh::LeanObject,
    mut v_x_4321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4327_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u64 = 0;
    let mut v___x_4330_: u64 = 0;
    let mut v___x_4331_: u64 = 0;
    let mut v_fold_4332_: u64 = 0;
    let mut v___x_4333_: u64 = 0;
    let mut v___x_4334_: u64 = 0;
    let mut v___x_4335_: u64 = 0;
    let mut v___x_4336_: usize = 0;
    let mut v___x_4337_: usize = 0;
    let mut v___x_4338_: usize = 0;
    let mut v___x_4339_: usize = 0;
    let mut v___x_4340_: usize = 0;
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4321_) == 0 {
                    return v_x_4320_;
                } else {
                    v_key_4322_ = crate::leanh::lean_ctor_get(v_x_4321_, 0);
                    v_value_4323_ = crate::leanh::lean_ctor_get(v_x_4321_, 1);
                    v_tail_4324_ = crate::leanh::lean_ctor_get(v_x_4321_, 2);
                    v_isSharedCheck_4347_ = (!crate::leanh::lean_is_exclusive(v_x_4321_)) as u8;
                    if v_isSharedCheck_4347_ == 0 {
                        v___x_4326_ = v_x_4321_;
                        v_isShared_4327_ = v_isSharedCheck_4347_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4324_);
                        crate::leanh::lean_inc(v_value_4323_);
                        crate::leanh::lean_inc(v_key_4322_);
                        crate::leanh::lean_dec(v_x_4321_);
                        v___x_4326_ = crate::leanh::lean_box(0);
                        v_isShared_4327_ = v_isSharedCheck_4347_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4328_ = lean_array_get_size(v_x_4320_);
                v___x_4329_ = lean_uint64_of_nat(v_key_4322_);
                v___x_4330_ = 32u64;
                v___x_4331_ = lean_uint64_shift_right(v___x_4329_, v___x_4330_);
                v_fold_4332_ = lean_uint64_xor(v___x_4329_, v___x_4331_);
                v___x_4333_ = 16u64;
                v___x_4334_ = lean_uint64_shift_right(v_fold_4332_, v___x_4333_);
                v___x_4335_ = lean_uint64_xor(v_fold_4332_, v___x_4334_);
                v___x_4336_ = lean_uint64_to_usize(v___x_4335_);
                v___x_4337_ = lean_usize_of_nat(v___x_4328_);
                v___x_4338_ = 1usize;
                v___x_4339_ = lean_usize_sub(v___x_4337_, v___x_4338_);
                v___x_4340_ = lean_usize_land(v___x_4336_, v___x_4339_);
                v___x_4341_ = lean_array_uget_borrowed(v_x_4320_, v___x_4340_);
                crate::leanh::lean_inc(v___x_4341_);
                if v_isShared_4327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4326_, 2, v___x_4341_);
                    v___x_4343_ = v___x_4326_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4346_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_key_4322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 1, v_value_4323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 2, v___x_4341_);
                    v___x_4343_ = v_reuseFailAlloc_4346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4344_ = lean_array_uset(v_x_4320_, v___x_4340_, v___x_4343_);
                v_x_4320_ = v___x_4344_;
                v_x_4321_ = v_tail_4324_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(
    mut v_i_4348_: *mut crate::leanh::LeanObject,
    mut v_source_4349_: *mut crate::leanh::LeanObject,
    mut v_target_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: u8 = 0;
    let mut v_es_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4351_ = lean_array_get_size(v_source_4349_);
                v___x_4352_ = lean_nat_dec_lt(v_i_4348_, v___x_4351_);
                if v___x_4352_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4349_);
                    crate::leanh::lean_dec(v_i_4348_);
                    return v_target_4350_;
                } else {
                    v_es_4353_ = lean_array_fget(v_source_4349_, v_i_4348_);
                    v___x_4354_ = crate::leanh::lean_box(0);
                    v_source_4355_ = lean_array_fset(v_source_4349_, v_i_4348_, v___x_4354_);
                    v_target_4356_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4350_, v_es_4353_);
                    v___x_4357_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4358_ = lean_nat_add(v_i_4348_, v___x_4357_);
                    crate::leanh::lean_dec(v_i_4348_);
                    v_i_4348_ = v___x_4358_;
                    v_source_4349_ = v_source_4355_;
                    v_target_4350_ = v_target_4356_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(
    mut v_data_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4361_ = lean_array_get_size(v_data_4360_);
    v___x_4362_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4363_ = lean_nat_mul(v___x_4361_, v___x_4362_);
    v___x_4364_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4365_ = crate::leanh::lean_box(0);
    v___x_4366_ = lean_mk_array(v_nbuckets_4363_, v___x_4365_);
    v___x_4367_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_4364_, v_data_4360_, v___x_4366_);
    return v___x_4367_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(
    mut v_m_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_b_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u64 = 0;
    let mut v___x_4375_: u64 = 0;
    let mut v___x_4376_: u64 = 0;
    let mut v_fold_4377_: u64 = 0;
    let mut v___x_4378_: u64 = 0;
    let mut v___x_4379_: u64 = 0;
    let mut v___x_4380_: u64 = 0;
    let mut v___x_4381_: usize = 0;
    let mut v___x_4382_: usize = 0;
    let mut v___x_4383_: usize = 0;
    let mut v___x_4384_: usize = 0;
    let mut v___x_4385_: usize = 0;
    let mut v_bkt_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4390_: u8 = 0;
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: u8 = 0;
    let mut v_val_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4408_: u8 = 0;
    let mut v_unused_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4371_ = crate::leanh::lean_ctor_get(v_m_4368_, 0);
                v_buckets_4372_ = crate::leanh::lean_ctor_get(v_m_4368_, 1);
                v___x_4373_ = lean_array_get_size(v_buckets_4372_);
                v___x_4374_ = lean_uint64_of_nat(v_a_4369_);
                v___x_4375_ = 32u64;
                v___x_4376_ = lean_uint64_shift_right(v___x_4374_, v___x_4375_);
                v_fold_4377_ = lean_uint64_xor(v___x_4374_, v___x_4376_);
                v___x_4378_ = 16u64;
                v___x_4379_ = lean_uint64_shift_right(v_fold_4377_, v___x_4378_);
                v___x_4380_ = lean_uint64_xor(v_fold_4377_, v___x_4379_);
                v___x_4381_ = lean_uint64_to_usize(v___x_4380_);
                v___x_4382_ = lean_usize_of_nat(v___x_4373_);
                v___x_4383_ = 1usize;
                v___x_4384_ = lean_usize_sub(v___x_4382_, v___x_4383_);
                v___x_4385_ = lean_usize_land(v___x_4381_, v___x_4384_);
                v_bkt_4386_ = lean_array_uget_borrowed(v_buckets_4372_, v___x_4385_);
                v___x_4387_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_4369_, v_bkt_4386_);
                if v___x_4387_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_4372_);
                    crate::leanh::lean_inc(v_size_4371_);
                    v_isSharedCheck_4408_ = (!crate::leanh::lean_is_exclusive(v_m_4368_)) as u8;
                    if v_isSharedCheck_4408_ == 0 {
                        v_unused_4409_ = crate::leanh::lean_ctor_get(v_m_4368_, 1);
                        crate::leanh::lean_dec(v_unused_4409_);
                        v_unused_4410_ = crate::leanh::lean_ctor_get(v_m_4368_, 0);
                        crate::leanh::lean_dec(v_unused_4410_);
                        v___x_4389_ = v_m_4368_;
                        v_isShared_4390_ = v_isSharedCheck_4408_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4368_);
                        v___x_4389_ = crate::leanh::lean_box(0);
                        v_isShared_4390_ = v_isSharedCheck_4408_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4370_);
                    crate::leanh::lean_dec(v_a_4369_);
                    return v_m_4368_;
                }
            }
            1 => {
                v___x_4391_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_4392_ = lean_nat_add(v_size_4371_, v___x_4391_);
                crate::leanh::lean_dec(v_size_4371_);
                crate::leanh::lean_inc(v_bkt_4386_);
                v___x_4393_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4393_, 0, v_a_4369_);
                crate::leanh::lean_ctor_set(v___x_4393_, 1, v_b_4370_);
                crate::leanh::lean_ctor_set(v___x_4393_, 2, v_bkt_4386_);
                v_buckets_x27_4394_ = lean_array_uset(v_buckets_4372_, v___x_4385_, v___x_4393_);
                v___x_4395_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4396_ = lean_nat_mul(v_size_x27_4392_, v___x_4395_);
                v___x_4397_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4398_ = lean_nat_div(v___x_4396_, v___x_4397_);
                crate::leanh::lean_dec(v___x_4396_);
                v___x_4399_ = lean_array_get_size(v_buckets_x27_4394_);
                v___x_4400_ = lean_nat_dec_le(v___x_4398_, v___x_4399_);
                crate::leanh::lean_dec(v___x_4398_);
                if v___x_4400_ == 0 {
                    v_val_4401_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_4394_);
                    if v_isShared_4390_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4389_, 1, v_val_4401_);
                        crate::leanh::lean_ctor_set(v___x_4389_, 0, v_size_x27_4392_);
                        v___x_4403_ = v___x_4389_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_size_x27_4392_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_val_4401_);
                        v___x_4403_ = v_reuseFailAlloc_4404_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4390_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4389_, 1, v_buckets_x27_4394_);
                        crate::leanh::lean_ctor_set(v___x_4389_, 0, v_size_x27_4392_);
                        v___x_4406_ = v___x_4389_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4407_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_size_x27_4392_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_buckets_x27_4394_);
                        v___x_4406_ = v_reuseFailAlloc_4407_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4403_;
            }
            3 => {
                return v___x_4406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(
    mut v___x_4411_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4412_: *mut crate::leanh::LeanObject,
    mut v_b_4413_: *mut crate::leanh::LeanObject,
    mut v___y_4414_: *mut crate::leanh::LeanObject,
    mut v___y_4415_: *mut crate::leanh::LeanObject,
    mut v___y_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
    mut v___y_4418_: *mut crate::leanh::LeanObject,
    mut v___y_4419_: *mut crate::leanh::LeanObject,
    mut v___y_4420_: *mut crate::leanh::LeanObject,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: u8 = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_4440_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4443_: u8 = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariantAlts_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: u8 = 0;
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_4475_: u8 = 0;
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4478_: u8 = 0;
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut v_a_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4494_: u8 = 0;
    let mut v_reuseFailAlloc_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut v_a_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4412_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_4411_);
                    v___x_4423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4423_, 0, v_b_4413_);
                    return v___x_4423_;
                } else {
                    v_head_4424_ = crate::leanh::lean_ctor_get(v_as_x27_4412_, 0);
                    v_tail_4425_ = crate::leanh::lean_ctor_get(v_as_x27_4412_, 1);
                    crate::leanh::lean_inc(v_head_4424_);
                    v___x_4426_ = l_Lean_MVarId_getType(
                        v_head_4424_,
                        v___y_4418_,
                        v___y_4419_,
                        v___y_4420_,
                        v___y_4421_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4426_) == 0 {
                        v_a_4427_ = crate::leanh::lean_ctor_get(v___x_4426_, 0);
                        crate::leanh::lean_inc(v_a_4427_);
                        crate::leanh::lean_dec_ref_known(v___x_4426_, 1);
                        crate::leanh::lean_inc_ref(v___x_4411_);
                        v___x_4428_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(
                            v___x_4411_,
                            v_a_4427_,
                        );
                        crate::leanh::lean_dec(v_a_4427_);
                        if v___x_4428_ == 0 {
                            crate::leanh::lean_inc(v_head_4424_);
                            v___x_4429_ = lean_array_push(v_b_4413_, v_head_4424_);
                            v_as_x27_4412_ = v_tail_4425_;
                            v_b_4413_ = v___x_4429_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4431_ = lean_st_ref_get(v___y_4415_);
                            v___x_4432_ = lean_st_ref_take(v___y_4415_);
                            v_specBackwardRuleCache_4433_ =
                                crate::leanh::lean_ctor_get(v___x_4432_, 0);
                            v_splitBackwardRuleCache_4434_ =
                                crate::leanh::lean_ctor_get(v___x_4432_, 1);
                            v_invariants_4435_ = crate::leanh::lean_ctor_get(v___x_4432_, 2);
                            v_vcs_4436_ = crate::leanh::lean_ctor_get(v___x_4432_, 3);
                            v_simpState_4437_ = crate::leanh::lean_ctor_get(v___x_4432_, 4);
                            v_fuel_4438_ = crate::leanh::lean_ctor_get(v___x_4432_, 5);
                            v_inlineHandledInvariants_4439_ =
                                crate::leanh::lean_ctor_get(v___x_4432_, 6);
                            v_preTacFailed_4440_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_4432_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                            );
                            v_isSharedCheck_4496_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4432_)) as u8;
                            if v_isSharedCheck_4496_ == 0 {
                                v___x_4442_ = v___x_4432_;
                                v_isShared_4443_ = v_isSharedCheck_4496_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_inlineHandledInvariants_4439_);
                                crate::leanh::lean_inc(v_fuel_4438_);
                                crate::leanh::lean_inc(v_simpState_4437_);
                                crate::leanh::lean_inc(v_vcs_4436_);
                                crate::leanh::lean_inc(v_invariants_4435_);
                                crate::leanh::lean_inc(v_splitBackwardRuleCache_4434_);
                                crate::leanh::lean_inc(v_specBackwardRuleCache_4433_);
                                crate::leanh::lean_dec(v___x_4432_);
                                v___x_4442_ = crate::leanh::lean_box(0);
                                v_isShared_4443_ = v_isSharedCheck_4496_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4413_);
                        crate::leanh::lean_dec_ref(v___x_4411_);
                        v_a_4497_ = crate::leanh::lean_ctor_get(v___x_4426_, 0);
                        v_isSharedCheck_4504_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4426_)) as u8;
                        if v_isSharedCheck_4504_ == 0 {
                            v___x_4499_ = v___x_4426_;
                            v_isShared_4500_ = v_isSharedCheck_4504_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4497_);
                            crate::leanh::lean_dec(v___x_4426_);
                            v___x_4499_ = crate::leanh::lean_box(0);
                            v_isShared_4500_ = v_isSharedCheck_4504_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_4424_);
                v___x_4444_ = lean_array_push(v_invariants_4435_, v_head_4424_);
                if v_isShared_4443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4442_, 2, v___x_4444_);
                    v___x_4446_ = v___x_4442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4495_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4495_,
                        0,
                        v_specBackwardRuleCache_4433_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4495_,
                        1,
                        v_splitBackwardRuleCache_4434_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 2, v___x_4444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 3, v_vcs_4436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 4, v_simpState_4437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 5, v_fuel_4438_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4495_,
                        6,
                        v_inlineHandledInvariants_4439_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4495_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_preTacFailed_4440_,
                    );
                    v___x_4446_ = v_reuseFailAlloc_4495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4447_ = lean_st_ref_set(v___y_4415_, v___x_4446_);
                v_invariants_4448_ = crate::leanh::lean_ctor_get(v___x_4431_, 2);
                crate::leanh::lean_inc_ref(v_invariants_4448_);
                crate::leanh::lean_dec(v___x_4431_);
                v_invariantAlts_4449_ = crate::leanh::lean_ctor_get(v___y_4414_, 18);
                v___x_4450_ = lean_array_get_size(v_invariants_4448_);
                crate::leanh::lean_dec_ref(v_invariants_4448_);
                v___x_4451_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4452_ = lean_nat_add(v___x_4450_, v___x_4451_);
                crate::leanh::lean_inc(v_head_4424_);
                v___x_4453_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(
                    v_invariantAlts_4449_,
                    v___x_4452_,
                    v_head_4424_,
                    v___y_4416_,
                    v___y_4417_,
                    v___y_4418_,
                    v___y_4419_,
                    v___y_4420_,
                    v___y_4421_,
                );
                if crate::leanh::lean_obj_tag(v___x_4453_) == 0 {
                    v_a_4454_ = crate::leanh::lean_ctor_get(v___x_4453_, 0);
                    crate::leanh::lean_inc(v_a_4454_);
                    crate::leanh::lean_dec_ref_known(v___x_4453_, 1);
                    v___x_4455_ = (crate::leanh::lean_unbox(v_a_4454_) as u8);
                    crate::leanh::lean_dec(v_a_4454_);
                    if v___x_4455_ == 0 {
                        crate::leanh::lean_dec(v___x_4452_);
                        v___x_4456_ = 2;
                        crate::leanh::lean_inc(v_head_4424_);
                        v___x_4457_ =
                            l_Lean_MVarId_setKind___redArg(v_head_4424_, v___x_4456_, v___y_4419_);
                        if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4457_, 1);
                            v_as_x27_4412_ = v_tail_4425_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_4413_);
                            crate::leanh::lean_dec_ref(v___x_4411_);
                            v_a_4459_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                            v_isSharedCheck_4466_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                            if v_isSharedCheck_4466_ == 0 {
                                v___x_4461_ = v___x_4457_;
                                v_isShared_4462_ = v_isSharedCheck_4466_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4459_);
                                crate::leanh::lean_dec(v___x_4457_);
                                v___x_4461_ = crate::leanh::lean_box(0);
                                v_isShared_4462_ = v_isSharedCheck_4466_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_4467_ = lean_st_ref_take(v___y_4415_);
                        v_specBackwardRuleCache_4468_ = crate::leanh::lean_ctor_get(v___x_4467_, 0);
                        v_splitBackwardRuleCache_4469_ =
                            crate::leanh::lean_ctor_get(v___x_4467_, 1);
                        v_invariants_4470_ = crate::leanh::lean_ctor_get(v___x_4467_, 2);
                        v_vcs_4471_ = crate::leanh::lean_ctor_get(v___x_4467_, 3);
                        v_simpState_4472_ = crate::leanh::lean_ctor_get(v___x_4467_, 4);
                        v_fuel_4473_ = crate::leanh::lean_ctor_get(v___x_4467_, 5);
                        v_inlineHandledInvariants_4474_ =
                            crate::leanh::lean_ctor_get(v___x_4467_, 6);
                        v_preTacFailed_4475_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_4467_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        );
                        v_isSharedCheck_4486_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4467_)) as u8;
                        if v_isSharedCheck_4486_ == 0 {
                            v___x_4477_ = v___x_4467_;
                            v_isShared_4478_ = v_isSharedCheck_4486_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_inlineHandledInvariants_4474_);
                            crate::leanh::lean_inc(v_fuel_4473_);
                            crate::leanh::lean_inc(v_simpState_4472_);
                            crate::leanh::lean_inc(v_vcs_4471_);
                            crate::leanh::lean_inc(v_invariants_4470_);
                            crate::leanh::lean_inc(v_splitBackwardRuleCache_4469_);
                            crate::leanh::lean_inc(v_specBackwardRuleCache_4468_);
                            crate::leanh::lean_dec(v___x_4467_);
                            v___x_4477_ = crate::leanh::lean_box(0);
                            v_isShared_4478_ = v_isSharedCheck_4486_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4452_);
                    crate::leanh::lean_dec_ref(v_b_4413_);
                    crate::leanh::lean_dec_ref(v___x_4411_);
                    v_a_4487_ = crate::leanh::lean_ctor_get(v___x_4453_, 0);
                    v_isSharedCheck_4494_ = (!crate::leanh::lean_is_exclusive(v___x_4453_)) as u8;
                    if v_isSharedCheck_4494_ == 0 {
                        v___x_4489_ = v___x_4453_;
                        v_isShared_4490_ = v_isSharedCheck_4494_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4487_);
                        crate::leanh::lean_dec(v___x_4453_);
                        v___x_4489_ = crate::leanh::lean_box(0);
                        v_isShared_4490_ = v_isSharedCheck_4494_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4462_ == 0 {
                    v___x_4464_ = v___x_4461_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
                    v___x_4464_ = v_reuseFailAlloc_4465_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4464_;
            }
            5 => {
                v___x_4479_ = crate::leanh::lean_box(0);
                v___x_4480_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_4474_, v___x_4452_, v___x_4479_);
                if v_isShared_4478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4477_, 6, v___x_4480_);
                    v___x_4482_ = v___x_4477_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4485_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4485_,
                        0,
                        v_specBackwardRuleCache_4468_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4485_,
                        1,
                        v_splitBackwardRuleCache_4469_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 2, v_invariants_4470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 3, v_vcs_4471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 4, v_simpState_4472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 5, v_fuel_4473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 6, v___x_4480_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4485_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_preTacFailed_4475_,
                    );
                    v___x_4482_ = v_reuseFailAlloc_4485_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4483_ = lean_st_ref_set(v___y_4415_, v___x_4482_);
                v_as_x27_4412_ = v_tail_4425_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_4490_ == 0 {
                    v___x_4492_ = v___x_4489_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
                    v___x_4492_ = v_reuseFailAlloc_4493_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4492_;
            }
            9 => {
                if v_isShared_4500_ == 0 {
                    v___x_4502_ = v___x_4499_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(
    mut v___x_4505_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4506_: *mut crate::leanh::LeanObject,
    mut v_b_4507_: *mut crate::leanh::LeanObject,
    mut v___y_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4517_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_4505_, v_as_x27_4506_, v_b_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
    crate::leanh::lean_dec(v___y_4515_);
    crate::leanh::lean_dec_ref(v___y_4514_);
    crate::leanh::lean_dec(v___y_4513_);
    crate::leanh::lean_dec_ref(v___y_4512_);
    crate::leanh::lean_dec(v___y_4511_);
    crate::leanh::lean_dec_ref(v___y_4510_);
    crate::leanh::lean_dec(v___y_4509_);
    crate::leanh::lean_dec_ref(v___y_4508_);
    crate::leanh::lean_dec(v_as_x27_4506_);
    return v_res_4517_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(
    mut v_subgoals_4520_: *mut crate::leanh::LeanObject,
    mut v_a_4521_: *mut crate::leanh::LeanObject,
    mut v_a_4522_: *mut crate::leanh::LeanObject,
    mut v_a_4523_: *mut crate::leanh::LeanObject,
    mut v_a_4524_: *mut crate::leanh::LeanObject,
    mut v_a_4525_: *mut crate::leanh::LeanObject,
    mut v_a_4526_: *mut crate::leanh::LeanObject,
    mut v_a_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4533_ = lean_st_ref_get(v_a_4531_);
    v_env_4534_ = crate::leanh::lean_ctor_get(v___x_4533_, 0);
    crate::leanh::lean_inc_ref(v_env_4534_);
    crate::leanh::lean_dec(v___x_4533_);
    v___x_4535_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0;
    v___x_4536_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_4534_, v_subgoals_4520_, v___x_4535_, v_a_4521_, v_a_4522_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
    return v___x_4536_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(
    mut v_subgoals_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
    mut v_a_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
    mut v_a_4544_: *mut crate::leanh::LeanObject,
    mut v_a_4545_: *mut crate::leanh::LeanObject,
    mut v_a_4546_: *mut crate::leanh::LeanObject,
    mut v_a_4547_: *mut crate::leanh::LeanObject,
    mut v_a_4548_: *mut crate::leanh::LeanObject,
    mut v_a_4549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4550_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
    crate::leanh::lean_dec(v_a_4548_);
    crate::leanh::lean_dec_ref(v_a_4547_);
    crate::leanh::lean_dec(v_a_4546_);
    crate::leanh::lean_dec_ref(v_a_4545_);
    crate::leanh::lean_dec(v_a_4544_);
    crate::leanh::lean_dec_ref(v_a_4543_);
    crate::leanh::lean_dec(v_a_4542_);
    crate::leanh::lean_dec_ref(v_a_4541_);
    crate::leanh::lean_dec(v_a_4540_);
    crate::leanh::lean_dec(v_a_4539_);
    crate::leanh::lean_dec_ref(v_a_4538_);
    crate::leanh::lean_dec(v_subgoals_4537_);
    return v_res_4550_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(
    mut v_00_u03b2_4551_: *mut crate::leanh::LeanObject,
    mut v_m_4552_: *mut crate::leanh::LeanObject,
    mut v_a_4553_: *mut crate::leanh::LeanObject,
    mut v_b_4554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4555_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_4552_, v_a_4553_, v_b_4554_);
    return v___x_4555_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(
    mut v___x_4556_: *mut crate::leanh::LeanObject,
    mut v_as_4557_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4558_: *mut crate::leanh::LeanObject,
    mut v_b_4559_: *mut crate::leanh::LeanObject,
    mut v_a_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
    mut v___y_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4573_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_4556_, v_as_x27_4558_, v_b_4559_, v___y_4561_, v___y_4562_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
    return v___x_4573_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4574_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_4575_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_x27_4576_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_b_4577_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_4578_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_4579_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4580_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4581_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4582_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4583_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4584_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4585_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4586_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4587_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4588_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4589_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4590_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4591_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(v___x_4574_, v_as_4575_, v_as_x27_4576_, v_b_4577_, v_a_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
    crate::leanh::lean_dec(v___y_4589_);
    crate::leanh::lean_dec_ref(v___y_4588_);
    crate::leanh::lean_dec(v___y_4587_);
    crate::leanh::lean_dec_ref(v___y_4586_);
    crate::leanh::lean_dec(v___y_4585_);
    crate::leanh::lean_dec_ref(v___y_4584_);
    crate::leanh::lean_dec(v___y_4583_);
    crate::leanh::lean_dec_ref(v___y_4582_);
    crate::leanh::lean_dec(v___y_4581_);
    crate::leanh::lean_dec(v___y_4580_);
    crate::leanh::lean_dec_ref(v___y_4579_);
    crate::leanh::lean_dec(v_as_x27_4576_);
    crate::leanh::lean_dec(v_as_4575_);
    return v_res_4591_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(
    mut v_00_u03b2_4592_: *mut crate::leanh::LeanObject,
    mut v_a_4593_: *mut crate::leanh::LeanObject,
    mut v_x_4594_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4595_: u8 = 0;
    v___x_4595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_4593_, v_x_4594_);
    return v___x_4595_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(
    mut v_00_u03b2_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
    mut v_x_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4599_: u8 = 0;
    let mut v_r_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4599_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_4596_, v_a_4597_, v_x_4598_);
    crate::leanh::lean_dec(v_x_4598_);
    crate::leanh::lean_dec(v_a_4597_);
    v_r_4600_ = crate::leanh::lean_box((v_res_4599_) as usize);
    return v_r_4600_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(
    mut v_00_u03b2_4601_: *mut crate::leanh::LeanObject,
    mut v_data_4602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4603_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_4602_);
    return v___x_4603_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4604_: *mut crate::leanh::LeanObject,
    mut v_i_4605_: *mut crate::leanh::LeanObject,
    mut v_source_4606_: *mut crate::leanh::LeanObject,
    mut v_target_4607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4608_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_4605_, v_source_4606_, v_target_4607_);
    return v___x_4608_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4609_: *mut crate::leanh::LeanObject,
    mut v_x_4610_: *mut crate::leanh::LeanObject,
    mut v_x_4611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4612_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4610_, v_x_4611_);
    return v___x_4612_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(
    mut v_as_x27_4613_: *mut crate::leanh::LeanObject,
    mut v_b_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4628_: u8 = 0;
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4613_) == 0 {
                    v___x_4617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4617_, 0, v_b_4614_);
                    return v___x_4617_;
                } else {
                    v_head_4618_ = crate::leanh::lean_ctor_get(v_as_x27_4613_, 0);
                    v_tail_4619_ = crate::leanh::lean_ctor_get(v_as_x27_4613_, 1);
                    v_mvarId_4620_ = crate::leanh::lean_ctor_get(v_head_4618_, 1);
                    v___x_4621_ = 2;
                    crate::leanh::lean_inc(v_mvarId_4620_);
                    v___x_4622_ =
                        l_Lean_MVarId_setKind___redArg(v_mvarId_4620_, v___x_4621_, v___y_4615_);
                    if crate::leanh::lean_obj_tag(v___x_4622_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4622_, 1);
                        crate::leanh::lean_inc(v_head_4618_);
                        v___x_4623_ = lean_array_push(v_b_4614_, v_head_4618_);
                        v_as_x27_4613_ = v_tail_4619_;
                        v_b_4614_ = v___x_4623_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4614_);
                        v_a_4625_ = crate::leanh::lean_ctor_get(v___x_4622_, 0);
                        v_isSharedCheck_4632_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4622_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4627_ = v___x_4622_;
                            v_isShared_4628_ = v_isSharedCheck_4632_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4625_);
                            crate::leanh::lean_dec(v___x_4622_);
                            v___x_4627_ = crate::leanh::lean_box(0);
                            v_isShared_4628_ = v_isSharedCheck_4632_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4628_ == 0 {
                    v___x_4630_ = v___x_4627_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg___boxed(
    mut v_as_x27_4633_: *mut crate::leanh::LeanObject,
    mut v_b_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4637_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(
            v_as_x27_4633_,
            v_b_4634_,
            v___y_4635_,
        );
    crate::leanh::lean_dec(v___y_4635_);
    crate::leanh::lean_dec(v_as_x27_4633_);
    return v_res_4637_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(
    mut v_goal_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_a_4643_: *mut crate::leanh::LeanObject,
    mut v_a_4644_: *mut crate::leanh::LeanObject,
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v_a_4646_: *mut crate::leanh::LeanObject,
    mut v_a_4647_: *mut crate::leanh::LeanObject,
    mut v_a_4648_: *mut crate::leanh::LeanObject,
    mut v_a_4649_: *mut crate::leanh::LeanObject,
    mut v_a_4650_: *mut crate::leanh::LeanObject,
    mut v_a_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preTac_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trivial_4654_: u8 = 0;
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4674_: u8 = 0;
    let mut v_preTac_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_4693_: u8 = 0;
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4696_: u8 = 0;
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4706_: u8 = 0;
    let mut v_isSharedCheck_4707_: u8 = 0;
    let mut v_a_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4711_: u8 = 0;
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4715_: u8 = 0;
    let mut v_a_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4723_: u8 = 0;
    let mut v_reuseFailAlloc_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_unused_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v_val_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4739_: u8 = 0;
    let mut v_a_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4743_: u8 = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4747_: u8 = 0;
    let mut v_a_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_preTac_4653_ = crate::leanh::lean_ctor_get(v_a_4641_, 17);
                v_trivial_4654_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4641_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                );
                v___x_4655_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(
                        v_preTac_4653_,
                        v_goal_4640_,
                        v_a_4643_,
                        v_a_4644_,
                        v_a_4645_,
                        v_a_4646_,
                        v_a_4647_,
                        v_a_4648_,
                        v_a_4649_,
                        v_a_4650_,
                        v_a_4651_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4655_) == 0 {
                    v_a_4656_ = crate::leanh::lean_ctor_get(v___x_4655_, 0);
                    crate::leanh::lean_inc(v_a_4656_);
                    crate::leanh::lean_dec_ref_known(v___x_4655_, 1);
                    v___x_4657_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0;
                    if v_trivial_4654_ == 0 {
                        v_mvarId_4727_ = crate::leanh::lean_ctor_get(v_a_4656_, 1);
                        crate::leanh::lean_inc(v_mvarId_4727_);
                        v_mvarId_4659_ = v_mvarId_4727_;
                        v___y_4660_ = v_a_4641_;
                        v___y_4661_ = v_a_4642_;
                        v___y_4662_ = v_a_4643_;
                        v___y_4663_ = v_a_4644_;
                        v___y_4664_ = v_a_4645_;
                        v___y_4665_ = v_a_4646_;
                        v___y_4666_ = v_a_4647_;
                        v___y_4667_ = v_a_4648_;
                        v___y_4668_ = v_a_4649_;
                        v___y_4669_ = v_a_4650_;
                        v___y_4670_ = v_a_4651_;
                        state = 1;
                        continue;
                    } else {
                        v_mvarId_4728_ = crate::leanh::lean_ctor_get(v_a_4656_, 1);
                        crate::leanh::lean_inc(v_mvarId_4728_);
                        v___x_4729_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
                            v_mvarId_4728_,
                            v_a_4641_,
                            v_a_4642_,
                            v_a_4643_,
                            v_a_4644_,
                            v_a_4645_,
                            v_a_4646_,
                            v_a_4647_,
                            v_a_4648_,
                            v_a_4649_,
                            v_a_4650_,
                            v_a_4651_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4729_) == 0 {
                            v_a_4730_ = crate::leanh::lean_ctor_get(v___x_4729_, 0);
                            v_isSharedCheck_4739_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4729_)) as u8;
                            if v_isSharedCheck_4739_ == 0 {
                                v___x_4732_ = v___x_4729_;
                                v_isShared_4733_ = v_isSharedCheck_4739_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4730_);
                                crate::leanh::lean_dec(v___x_4729_);
                                v___x_4732_ = crate::leanh::lean_box(0);
                                v_isShared_4733_ = v_isSharedCheck_4739_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4656_);
                            v_a_4740_ = crate::leanh::lean_ctor_get(v___x_4729_, 0);
                            v_isSharedCheck_4747_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4729_)) as u8;
                            if v_isSharedCheck_4747_ == 0 {
                                v___x_4742_ = v___x_4729_;
                                v_isShared_4743_ = v_isSharedCheck_4747_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4740_);
                                crate::leanh::lean_dec(v___x_4729_);
                                v___x_4742_ = crate::leanh::lean_box(0);
                                v_isShared_4743_ = v_isSharedCheck_4747_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_4748_ = crate::leanh::lean_ctor_get(v___x_4655_, 0);
                    v_isSharedCheck_4755_ = (!crate::leanh::lean_is_exclusive(v___x_4655_)) as u8;
                    if v_isSharedCheck_4755_ == 0 {
                        v___x_4750_ = v___x_4655_;
                        v_isShared_4751_ = v_isSharedCheck_4755_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4748_);
                        crate::leanh::lean_dec(v___x_4655_);
                        v___x_4750_ = crate::leanh::lean_box(0);
                        v_isShared_4751_ = v_isSharedCheck_4755_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_toGoalState_4671_ = crate::leanh::lean_ctor_get(v_a_4656_, 0);
                v_isSharedCheck_4725_ = (!crate::leanh::lean_is_exclusive(v_a_4656_)) as u8;
                if v_isSharedCheck_4725_ == 0 {
                    v_unused_4726_ = crate::leanh::lean_ctor_get(v_a_4656_, 1);
                    crate::leanh::lean_dec(v_unused_4726_);
                    v___x_4673_ = v_a_4656_;
                    v_isShared_4674_ = v_isSharedCheck_4725_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toGoalState_4671_);
                    crate::leanh::lean_dec(v_a_4656_);
                    v___x_4673_ = crate::leanh::lean_box(0);
                    v_isShared_4674_ = v_isSharedCheck_4725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_preTac_4675_ = crate::leanh::lean_ctor_get(v___y_4660_, 17);
                if v_isShared_4674_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4673_, 1, v_mvarId_4659_);
                    v___x_4677_ = v___x_4673_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4724_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_toGoalState_4671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4724_, 1, v_mvarId_4659_);
                    v___x_4677_ = v_reuseFailAlloc_4724_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_preTac_4675_);
                v___x_4678_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(
                    v_preTac_4675_,
                    v___x_4677_,
                    v___y_4660_,
                    v___y_4661_,
                    v___y_4662_,
                    v___y_4663_,
                    v___y_4664_,
                    v___y_4665_,
                    v___y_4666_,
                    v___y_4667_,
                    v___y_4668_,
                    v___y_4669_,
                    v___y_4670_,
                );
                if crate::leanh::lean_obj_tag(v___x_4678_) == 0 {
                    v_a_4679_ = crate::leanh::lean_ctor_get(v___x_4678_, 0);
                    crate::leanh::lean_inc(v_a_4679_);
                    crate::leanh::lean_dec_ref_known(v___x_4678_, 1);
                    v___x_4680_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(v_a_4679_, v___x_4657_, v___y_4668_);
                    crate::leanh::lean_dec(v_a_4679_);
                    if crate::leanh::lean_obj_tag(v___x_4680_) == 0 {
                        v_a_4681_ = crate::leanh::lean_ctor_get(v___x_4680_, 0);
                        v_isSharedCheck_4707_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4680_)) as u8;
                        if v_isSharedCheck_4707_ == 0 {
                            v___x_4683_ = v___x_4680_;
                            v_isShared_4684_ = v_isSharedCheck_4707_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4681_);
                            crate::leanh::lean_dec(v___x_4680_);
                            v___x_4683_ = crate::leanh::lean_box(0);
                            v_isShared_4684_ = v_isSharedCheck_4707_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_4708_ = crate::leanh::lean_ctor_get(v___x_4680_, 0);
                        v_isSharedCheck_4715_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4680_)) as u8;
                        if v_isSharedCheck_4715_ == 0 {
                            v___x_4710_ = v___x_4680_;
                            v_isShared_4711_ = v_isSharedCheck_4715_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4708_);
                            crate::leanh::lean_dec(v___x_4680_);
                            v___x_4710_ = crate::leanh::lean_box(0);
                            v_isShared_4711_ = v_isSharedCheck_4715_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_4716_ = crate::leanh::lean_ctor_get(v___x_4678_, 0);
                    v_isSharedCheck_4723_ = (!crate::leanh::lean_is_exclusive(v___x_4678_)) as u8;
                    if v_isSharedCheck_4723_ == 0 {
                        v___x_4718_ = v___x_4678_;
                        v_isShared_4719_ = v_isSharedCheck_4723_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4716_);
                        crate::leanh::lean_dec(v___x_4678_);
                        v___x_4718_ = crate::leanh::lean_box(0);
                        v_isShared_4719_ = v_isSharedCheck_4723_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4685_ = lean_st_ref_take(v___y_4661_);
                v_specBackwardRuleCache_4686_ = crate::leanh::lean_ctor_get(v___x_4685_, 0);
                v_splitBackwardRuleCache_4687_ = crate::leanh::lean_ctor_get(v___x_4685_, 1);
                v_invariants_4688_ = crate::leanh::lean_ctor_get(v___x_4685_, 2);
                v_vcs_4689_ = crate::leanh::lean_ctor_get(v___x_4685_, 3);
                v_simpState_4690_ = crate::leanh::lean_ctor_get(v___x_4685_, 4);
                v_fuel_4691_ = crate::leanh::lean_ctor_get(v___x_4685_, 5);
                v_inlineHandledInvariants_4692_ = crate::leanh::lean_ctor_get(v___x_4685_, 6);
                v_preTacFailed_4693_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4685_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_4706_ = (!crate::leanh::lean_is_exclusive(v___x_4685_)) as u8;
                if v_isSharedCheck_4706_ == 0 {
                    v___x_4695_ = v___x_4685_;
                    v_isShared_4696_ = v_isSharedCheck_4706_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineHandledInvariants_4692_);
                    crate::leanh::lean_inc(v_fuel_4691_);
                    crate::leanh::lean_inc(v_simpState_4690_);
                    crate::leanh::lean_inc(v_vcs_4689_);
                    crate::leanh::lean_inc(v_invariants_4688_);
                    crate::leanh::lean_inc(v_splitBackwardRuleCache_4687_);
                    crate::leanh::lean_inc(v_specBackwardRuleCache_4686_);
                    crate::leanh::lean_dec(v___x_4685_);
                    v___x_4695_ = crate::leanh::lean_box(0);
                    v_isShared_4696_ = v_isSharedCheck_4706_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4697_ = l_Array_append___redArg(v_vcs_4689_, v_a_4681_);
                crate::leanh::lean_dec(v_a_4681_);
                if v_isShared_4696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4695_, 3, v___x_4697_);
                    v___x_4699_ = v___x_4695_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4705_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4705_,
                        0,
                        v_specBackwardRuleCache_4686_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4705_,
                        1,
                        v_splitBackwardRuleCache_4687_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 2, v_invariants_4688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 3, v___x_4697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 4, v_simpState_4690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 5, v_fuel_4691_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4705_,
                        6,
                        v_inlineHandledInvariants_4692_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4705_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_preTacFailed_4693_,
                    );
                    v___x_4699_ = v_reuseFailAlloc_4705_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4700_ = lean_st_ref_set(v___y_4661_, v___x_4699_);
                v___x_4701_ = crate::leanh::lean_box(0);
                if v_isShared_4684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4683_, 0, v___x_4701_);
                    v___x_4703_ = v___x_4683_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4701_);
                    v___x_4703_ = v_reuseFailAlloc_4704_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4703_;
            }
            8 => {
                if v_isShared_4711_ == 0 {
                    v___x_4713_ = v___x_4710_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
                    v___x_4713_ = v_reuseFailAlloc_4714_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4713_;
            }
            10 => {
                if v_isShared_4719_ == 0 {
                    v___x_4721_ = v___x_4718_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
                    v___x_4721_ = v_reuseFailAlloc_4722_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4721_;
            }
            12 => {
                if crate::leanh::lean_obj_tag(v_a_4730_) == 1 {
                    crate::leanh::lean_del_object(v___x_4732_);
                    v_val_4734_ = crate::leanh::lean_ctor_get(v_a_4730_, 0);
                    crate::leanh::lean_inc(v_val_4734_);
                    crate::leanh::lean_dec_ref_known(v_a_4730_, 1);
                    v_mvarId_4659_ = v_val_4734_;
                    v___y_4660_ = v_a_4641_;
                    v___y_4661_ = v_a_4642_;
                    v___y_4662_ = v_a_4643_;
                    v___y_4663_ = v_a_4644_;
                    v___y_4664_ = v_a_4645_;
                    v___y_4665_ = v_a_4646_;
                    v___y_4666_ = v_a_4647_;
                    v___y_4667_ = v_a_4648_;
                    v___y_4668_ = v_a_4649_;
                    v___y_4669_ = v_a_4650_;
                    v___y_4670_ = v_a_4651_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4730_);
                    crate::leanh::lean_dec(v_a_4656_);
                    v___x_4735_ = crate::leanh::lean_box(0);
                    if v_isShared_4733_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4732_, 0, v___x_4735_);
                        v___x_4737_ = v___x_4732_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4738_, 0, v___x_4735_);
                        v___x_4737_ = v_reuseFailAlloc_4738_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_4737_;
            }
            14 => {
                if v_isShared_4743_ == 0 {
                    v___x_4745_ = v___x_4742_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
                    v___x_4745_ = v_reuseFailAlloc_4746_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4745_;
            }
            16 => {
                if v_isShared_4751_ == 0 {
                    v___x_4753_ = v___x_4750_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
                    v___x_4753_ = v_reuseFailAlloc_4754_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(
    mut v_goal_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
    mut v_a_4760_: *mut crate::leanh::LeanObject,
    mut v_a_4761_: *mut crate::leanh::LeanObject,
    mut v_a_4762_: *mut crate::leanh::LeanObject,
    mut v_a_4763_: *mut crate::leanh::LeanObject,
    mut v_a_4764_: *mut crate::leanh::LeanObject,
    mut v_a_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4769_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(
        v_goal_4756_,
        v_a_4757_,
        v_a_4758_,
        v_a_4759_,
        v_a_4760_,
        v_a_4761_,
        v_a_4762_,
        v_a_4763_,
        v_a_4764_,
        v_a_4765_,
        v_a_4766_,
        v_a_4767_,
    );
    crate::leanh::lean_dec(v_a_4767_);
    crate::leanh::lean_dec_ref(v_a_4766_);
    crate::leanh::lean_dec(v_a_4765_);
    crate::leanh::lean_dec_ref(v_a_4764_);
    crate::leanh::lean_dec(v_a_4763_);
    crate::leanh::lean_dec_ref(v_a_4762_);
    crate::leanh::lean_dec(v_a_4761_);
    crate::leanh::lean_dec_ref(v_a_4760_);
    crate::leanh::lean_dec(v_a_4759_);
    crate::leanh::lean_dec(v_a_4758_);
    crate::leanh::lean_dec_ref(v_a_4757_);
    return v_res_4769_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(
    mut v_as_4770_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4771_: *mut crate::leanh::LeanObject,
    mut v_b_4772_: *mut crate::leanh::LeanObject,
    mut v_a_4773_: *mut crate::leanh::LeanObject,
    mut v___y_4774_: *mut crate::leanh::LeanObject,
    mut v___y_4775_: *mut crate::leanh::LeanObject,
    mut v___y_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
    mut v___y_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4786_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(
            v_as_x27_4771_,
            v_b_4772_,
            v___y_4782_,
        );
    return v___x_4786_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___boxed(
    mut v_as_4787_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4788_: *mut crate::leanh::LeanObject,
    mut v_b_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
    mut v___y_4802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4803_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(
        v_as_4787_,
        v_as_x27_4788_,
        v_b_4789_,
        v_a_4790_,
        v___y_4791_,
        v___y_4792_,
        v___y_4793_,
        v___y_4794_,
        v___y_4795_,
        v___y_4796_,
        v___y_4797_,
        v___y_4798_,
        v___y_4799_,
        v___y_4800_,
        v___y_4801_,
    );
    crate::leanh::lean_dec(v___y_4801_);
    crate::leanh::lean_dec_ref(v___y_4800_);
    crate::leanh::lean_dec(v___y_4799_);
    crate::leanh::lean_dec_ref(v___y_4798_);
    crate::leanh::lean_dec(v___y_4797_);
    crate::leanh::lean_dec_ref(v___y_4796_);
    crate::leanh::lean_dec(v___y_4795_);
    crate::leanh::lean_dec_ref(v___y_4794_);
    crate::leanh::lean_dec(v___y_4793_);
    crate::leanh::lean_dec(v___y_4792_);
    crate::leanh::lean_dec_ref(v___y_4791_);
    crate::leanh::lean_dec(v_as_x27_4788_);
    crate::leanh::lean_dec(v_as_4787_);
    return v_res_4803_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(
    mut v_msg_4804_: *mut crate::leanh::LeanObject,
    mut v___y_4805_: *mut crate::leanh::LeanObject,
    mut v___y_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4815_: u8 = 0;
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4810_ = crate::leanh::lean_ctor_get(v___y_4807_, 5);
                v___x_4811_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v_msg_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
                v_a_4812_ = crate::leanh::lean_ctor_get(v___x_4811_, 0);
                v_isSharedCheck_4820_ = (!crate::leanh::lean_is_exclusive(v___x_4811_)) as u8;
                if v_isSharedCheck_4820_ == 0 {
                    v___x_4814_ = v___x_4811_;
                    v_isShared_4815_ = v_isSharedCheck_4820_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4812_);
                    crate::leanh::lean_dec(v___x_4811_);
                    v___x_4814_ = crate::leanh::lean_box(0);
                    v_isShared_4815_ = v_isSharedCheck_4820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4810_);
                v___x_4816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4816_, 0, v_ref_4810_);
                crate::leanh::lean_ctor_set(v___x_4816_, 1, v_a_4812_);
                if v_isShared_4815_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4814_, 1);
                    crate::leanh::lean_ctor_set(v___x_4814_, 0, v___x_4816_);
                    v___x_4818_ = v___x_4814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4816_);
                    v___x_4818_ = v_reuseFailAlloc_4819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg___boxed(
    mut v_msg_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4827_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(
            v_msg_4821_,
            v___y_4822_,
            v___y_4823_,
            v___y_4824_,
            v___y_4825_,
        );
    crate::leanh::lean_dec(v___y_4825_);
    crate::leanh::lean_dec_ref(v___y_4824_);
    crate::leanh::lean_dec(v___y_4823_);
    crate::leanh::lean_dec_ref(v___y_4822_);
    return v_res_4827_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(
    mut v_00_u03b1_4828_: *mut crate::leanh::LeanObject,
    mut v_msg_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
    mut v___y_4831_: *mut crate::leanh::LeanObject,
    mut v___y_4832_: *mut crate::leanh::LeanObject,
    mut v___y_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
    mut v___y_4836_: *mut crate::leanh::LeanObject,
    mut v___y_4837_: *mut crate::leanh::LeanObject,
    mut v___y_4838_: *mut crate::leanh::LeanObject,
    mut v___y_4839_: *mut crate::leanh::LeanObject,
    mut v___y_4840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4842_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(
            v_msg_4829_,
            v___y_4837_,
            v___y_4838_,
            v___y_4839_,
            v___y_4840_,
        );
    return v___x_4842_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(
    mut v_00_u03b1_4843_: *mut crate::leanh::LeanObject,
    mut v_msg_4844_: *mut crate::leanh::LeanObject,
    mut v___y_4845_: *mut crate::leanh::LeanObject,
    mut v___y_4846_: *mut crate::leanh::LeanObject,
    mut v___y_4847_: *mut crate::leanh::LeanObject,
    mut v___y_4848_: *mut crate::leanh::LeanObject,
    mut v___y_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
    mut v___y_4851_: *mut crate::leanh::LeanObject,
    mut v___y_4852_: *mut crate::leanh::LeanObject,
    mut v___y_4853_: *mut crate::leanh::LeanObject,
    mut v___y_4854_: *mut crate::leanh::LeanObject,
    mut v___y_4855_: *mut crate::leanh::LeanObject,
    mut v___y_4856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4857_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(
        v_00_u03b1_4843_,
        v_msg_4844_,
        v___y_4845_,
        v___y_4846_,
        v___y_4847_,
        v___y_4848_,
        v___y_4849_,
        v___y_4850_,
        v___y_4851_,
        v___y_4852_,
        v___y_4853_,
        v___y_4854_,
        v___y_4855_,
    );
    crate::leanh::lean_dec(v___y_4855_);
    crate::leanh::lean_dec_ref(v___y_4854_);
    crate::leanh::lean_dec(v___y_4853_);
    crate::leanh::lean_dec_ref(v___y_4852_);
    crate::leanh::lean_dec(v___y_4851_);
    crate::leanh::lean_dec_ref(v___y_4850_);
    crate::leanh::lean_dec(v___y_4849_);
    crate::leanh::lean_dec_ref(v___y_4848_);
    crate::leanh::lean_dec(v___y_4847_);
    crate::leanh::lean_dec(v___y_4846_);
    crate::leanh::lean_dec_ref(v___y_4845_);
    return v_res_4857_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(
    mut v_goal_4858_: *mut crate::leanh::LeanObject,
    mut v_scope_4859_: *mut crate::leanh::LeanObject,
    mut v_sz_4860_: usize,
    mut v_i_4861_: usize,
    mut v_bs_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4863_: u8 = 0;
    let mut v_toGoalState_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: usize = 0;
    let mut v___x_4871_: usize = 0;
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4863_ = lean_usize_dec_lt(v_i_4861_, v_sz_4860_);
                if v___x_4863_ == 0 {
                    crate::leanh::lean_dec_ref(v_scope_4859_);
                    return v_bs_4862_;
                } else {
                    v_toGoalState_4864_ = crate::leanh::lean_ctor_get(v_goal_4858_, 0);
                    v_v_4865_ = lean_array_uget(v_bs_4862_, v_i_4861_);
                    v___x_4866_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4867_ = lean_array_uset(v_bs_4862_, v_i_4861_, v___x_4866_);
                    crate::leanh::lean_inc_ref(v_toGoalState_4864_);
                    v___x_4868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4868_, 0, v_toGoalState_4864_);
                    crate::leanh::lean_ctor_set(v___x_4868_, 1, v_v_4865_);
                    crate::leanh::lean_inc_ref(v_scope_4859_);
                    v___x_4869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4869_, 0, v___x_4868_);
                    crate::leanh::lean_ctor_set(v___x_4869_, 1, v_scope_4859_);
                    v___x_4870_ = 1usize;
                    v___x_4871_ = lean_usize_add(v_i_4861_, v___x_4870_);
                    v___x_4872_ = lean_array_uset(v_bs_x27_4867_, v_i_4861_, v___x_4869_);
                    v_i_4861_ = v___x_4871_;
                    v_bs_4862_ = v___x_4872_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3___boxed(
    mut v_goal_4874_: *mut crate::leanh::LeanObject,
    mut v_scope_4875_: *mut crate::leanh::LeanObject,
    mut v_sz_4876_: *mut crate::leanh::LeanObject,
    mut v_i_4877_: *mut crate::leanh::LeanObject,
    mut v_bs_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4879_: usize = 0;
    let mut v_i_boxed_4880_: usize = 0;
    let mut v_res_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4879_ = crate::leanh::lean_unbox_usize(v_sz_4876_);
    crate::leanh::lean_dec(v_sz_4876_);
    v_i_boxed_4880_ = crate::leanh::lean_unbox_usize(v_i_4877_);
    crate::leanh::lean_dec(v_i_4877_);
    v_res_4881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(v_goal_4874_, v_scope_4875_, v_sz_boxed_4879_, v_i_boxed_4880_, v_bs_4878_);
    crate::leanh::lean_dec_ref(v_goal_4874_);
    return v_res_4881_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(
    mut v_a_4882_: *mut crate::leanh::LeanObject,
    mut v_scope_4883_: *mut crate::leanh::LeanObject,
    mut v___x_4884_: *mut crate::leanh::LeanObject,
    mut v_goal_4885_: *mut crate::leanh::LeanObject,
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
    mut v___y_4893_: *mut crate::leanh::LeanObject,
    mut v___y_4894_: *mut crate::leanh::LeanObject,
    mut v___y_4895_: *mut crate::leanh::LeanObject,
    mut v___y_4896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4899_: usize = 0;
    let mut v___x_4900_: usize = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4898_ = l_Array_reverse___redArg(v_a_4882_);
    v_sz_4899_ = lean_array_size(v___x_4898_);
    v___x_4900_ = 0usize;
    v___x_4901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(v_goal_4885_, v_scope_4883_, v_sz_4899_, v___x_4900_, v___x_4898_);
    v___x_4902_ = l_Array_append___redArg(v___x_4884_, v___x_4901_);
    crate::leanh::lean_dec_ref(v___x_4901_);
    v___x_4903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4903_, 0, v___x_4902_);
    v___x_4904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4904_, 0, v___x_4903_);
    return v___x_4904_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2___boxed(
    mut v_a_4905_: *mut crate::leanh::LeanObject,
    mut v_scope_4906_: *mut crate::leanh::LeanObject,
    mut v___x_4907_: *mut crate::leanh::LeanObject,
    mut v_goal_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
    mut v___y_4919_: *mut crate::leanh::LeanObject,
    mut v___y_4920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4921_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_4905_, v_scope_4906_, v___x_4907_, v_goal_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_);
    crate::leanh::lean_dec(v___y_4919_);
    crate::leanh::lean_dec_ref(v___y_4918_);
    crate::leanh::lean_dec(v___y_4917_);
    crate::leanh::lean_dec_ref(v___y_4916_);
    crate::leanh::lean_dec(v___y_4915_);
    crate::leanh::lean_dec_ref(v___y_4914_);
    crate::leanh::lean_dec(v___y_4913_);
    crate::leanh::lean_dec_ref(v___y_4912_);
    crate::leanh::lean_dec(v___y_4911_);
    crate::leanh::lean_dec(v___y_4910_);
    crate::leanh::lean_dec_ref(v___y_4909_);
    crate::leanh::lean_dec_ref(v_goal_4908_);
    return v_res_4921_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4923_ =
        l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0;
    v___x_4924_ = l_Lean_stringToMessageData(v___x_4923_);
    return v___x_4924_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4926_ =
        l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2;
    v___x_4927_ = l_Lean_stringToMessageData(v___x_4926_);
    return v___x_4927_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4929_ =
        l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4;
    v___x_4930_ = l_Lean_stringToMessageData(v___x_4929_);
    return v___x_4930_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4932_ =
        l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6;
    v___x_4933_ = l_Lean_stringToMessageData(v___x_4932_);
    return v___x_4933_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2(
    mut v_a_4934_: *mut crate::leanh::LeanObject,
    mut v_a_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___y_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4934_) == 0 {
                    v___x_4936_ = l_List_reverse___redArg(v_a_4935_);
                    return v___x_4936_;
                } else {
                    v_head_4937_ = crate::leanh::lean_ctor_get(v_a_4934_, 0);
                    v_tail_4938_ = crate::leanh::lean_ctor_get(v_a_4934_, 1);
                    v_isSharedCheck_4966_ = (!crate::leanh::lean_is_exclusive(v_a_4934_)) as u8;
                    if v_isSharedCheck_4966_ == 0 {
                        v___x_4940_ = v_a_4934_;
                        v_isShared_4941_ = v_isSharedCheck_4966_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4938_);
                        crate::leanh::lean_inc(v_head_4937_);
                        crate::leanh::lean_dec(v_a_4934_);
                        v___x_4940_ = crate::leanh::lean_box(0);
                        v_isShared_4941_ = v_isSharedCheck_4966_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_head_4937_) {
                0 => {
                    v_declName_4948_ = crate::leanh::lean_ctor_get(v_head_4937_, 0);
                    crate::leanh::lean_inc(v_declName_4948_);
                    crate::leanh::lean_dec_ref_known(v_head_4937_, 1);
                    v___x_4949_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1);
                    v___x_4950_ = l_Lean_MessageData_ofName(v_declName_4948_);
                    v___x_4951_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4951_, 0, v___x_4949_);
                    crate::leanh::lean_ctor_set(v___x_4951_, 1, v___x_4950_);
                    v___y_4943_ = v___x_4951_;
                    state = 2;
                    continue;
                }
                1 => {
                    v_fvarId_4952_ = crate::leanh::lean_ctor_get(v_head_4937_, 0);
                    crate::leanh::lean_inc(v_fvarId_4952_);
                    crate::leanh::lean_dec_ref_known(v_head_4937_, 1);
                    v___x_4953_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3_once), _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3);
                    v___x_4954_ = l_Lean_mkFVar(v_fvarId_4952_);
                    v___x_4955_ = l_Lean_MessageData_ofExpr(v___x_4954_);
                    v___x_4956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4956_, 0, v___x_4953_);
                    crate::leanh::lean_ctor_set(v___x_4956_, 1, v___x_4955_);
                    v___y_4943_ = v___x_4956_;
                    state = 2;
                    continue;
                }
                _ => {
                    v_ref_4957_ = crate::leanh::lean_ctor_get(v_head_4937_, 1);
                    crate::leanh::lean_inc(v_ref_4957_);
                    v_proof_4958_ = crate::leanh::lean_ctor_get(v_head_4937_, 2);
                    crate::leanh::lean_inc_ref(v_proof_4958_);
                    crate::leanh::lean_dec_ref_known(v_head_4937_, 3);
                    v___x_4959_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5_once), _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5);
                    v___x_4960_ = l_Lean_MessageData_ofSyntax(v_ref_4957_);
                    v___x_4961_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4961_, 0, v___x_4959_);
                    crate::leanh::lean_ctor_set(v___x_4961_, 1, v___x_4960_);
                    v___x_4962_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7_once), _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7);
                    v___x_4963_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4963_, 0, v___x_4961_);
                    crate::leanh::lean_ctor_set(v___x_4963_, 1, v___x_4962_);
                    v___x_4964_ = l_Lean_MessageData_ofExpr(v_proof_4958_);
                    v___x_4965_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4965_, 0, v___x_4963_);
                    crate::leanh::lean_ctor_set(v___x_4965_, 1, v___x_4964_);
                    v___y_4943_ = v___x_4965_;
                    state = 2;
                    continue;
                }
            },
            2 => {
                if v_isShared_4941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4940_, 1, v_a_4935_);
                    crate::leanh::lean_ctor_set(v___x_4940_, 0, v___y_4943_);
                    v___x_4945_ = v___x_4940_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___y_4943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 1, v_a_4935_);
                    v___x_4945_ = v_reuseFailAlloc_4947_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_4934_ = v_tail_4938_;
                v_a_4935_ = v___x_4945_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(
    mut v_sz_4967_: usize,
    mut v_i_4968_: usize,
    mut v_bs_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4970_: u8 = 0;
    let mut v_v_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: usize = 0;
    let mut v___x_4976_: usize = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4970_ = lean_usize_dec_lt(v_i_4968_, v_sz_4967_);
                if v___x_4970_ == 0 {
                    return v_bs_4969_;
                } else {
                    v_v_4971_ = lean_array_uget_borrowed(v_bs_4969_, v_i_4968_);
                    v_proof_4972_ = crate::leanh::lean_ctor_get(v_v_4971_, 1);
                    crate::leanh::lean_inc_ref(v_proof_4972_);
                    v___x_4973_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4974_ = lean_array_uset(v_bs_4969_, v_i_4968_, v___x_4973_);
                    v___x_4975_ = 1usize;
                    v___x_4976_ = lean_usize_add(v_i_4968_, v___x_4975_);
                    v___x_4977_ = lean_array_uset(v_bs_x27_4974_, v_i_4968_, v_proof_4972_);
                    v_i_4968_ = v___x_4976_;
                    v_bs_4969_ = v___x_4977_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(
    mut v_sz_4979_: *mut crate::leanh::LeanObject,
    mut v_i_4980_: *mut crate::leanh::LeanObject,
    mut v_bs_4981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4982_: usize = 0;
    let mut v_i_boxed_4983_: usize = 0;
    let mut v_res_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4982_ = crate::leanh::lean_unbox_usize(v_sz_4979_);
    crate::leanh::lean_dec(v_sz_4979_);
    v_i_boxed_4983_ = crate::leanh::lean_unbox_usize(v_i_4980_);
    crate::leanh::lean_dec(v_i_4980_);
    v_res_4984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_sz_boxed_4982_, v_i_boxed_4983_, v_bs_4981_);
    return v_res_4984_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0;
    v___x_4987_ = l_Lean_stringToMessageData(v___x_4986_);
    return v___x_4987_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2;
    v___x_4990_ = l_Lean_stringToMessageData(v___x_4989_);
    return v___x_4990_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4992_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4;
    v___x_4993_ = l_Lean_stringToMessageData(v___x_4992_);
    return v___x_4993_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4995_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6;
    v___x_4996_ = l_Lean_stringToMessageData(v___x_4995_);
    return v___x_4996_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4998_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8;
    v___x_4999_ = l_Lean_stringToMessageData(v___x_4998_);
    return v___x_4999_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1(
    mut v___x_5000_: u8,
    mut v_monad_5001_: *mut crate::leanh::LeanObject,
    mut v_e_5002_: *mut crate::leanh::LeanObject,
    mut v_thms_5003_: *mut crate::leanh::LeanObject,
    mut v___y_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
    mut v___y_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
    mut v___y_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v___x_5000_ == 0 {
        let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5025_: usize = 0;
        let mut v___x_5026_: usize = 0;
        let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5016_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1);
        v___x_5017_ = l_Lean_MessageData_ofExpr(v_monad_5001_);
        v___x_5018_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5018_, 0, v___x_5016_);
        crate::leanh::lean_ctor_set(v___x_5018_, 1, v___x_5017_);
        v___x_5019_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3);
        v___x_5020_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5020_, 0, v___x_5018_);
        crate::leanh::lean_ctor_set(v___x_5020_, 1, v___x_5019_);
        v___x_5021_ = l_Lean_MessageData_ofExpr(v_e_5002_);
        v___x_5022_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5022_, 0, v___x_5020_);
        crate::leanh::lean_ctor_set(v___x_5022_, 1, v___x_5021_);
        v___x_5023_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5);
        v___x_5024_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5024_, 0, v___x_5022_);
        crate::leanh::lean_ctor_set(v___x_5024_, 1, v___x_5023_);
        v_sz_5025_ = lean_array_size(v_thms_5003_);
        v___x_5026_ = 0usize;
        v___x_5027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_sz_5025_, v___x_5026_, v_thms_5003_);
        v___x_5028_ = lean_array_to_list(v___x_5027_);
        v___x_5029_ = crate::leanh::lean_box(0);
        v___x_5030_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2(
            v___x_5028_,
            v___x_5029_,
        );
        v___x_5031_ = l_Lean_MessageData_ofList(v___x_5030_);
        v___x_5032_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5032_, 0, v___x_5024_);
        crate::leanh::lean_ctor_set(v___x_5032_, 1, v___x_5031_);
        v___x_5033_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7);
        v___x_5034_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5034_, 0, v___x_5032_);
        crate::leanh::lean_ctor_set(v___x_5034_, 1, v___x_5033_);
        v___x_5035_ =
            l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(
                v___x_5034_,
                v___y_5011_,
                v___y_5012_,
                v___y_5013_,
                v___y_5014_,
            );
        return v___x_5035_;
    } else {
        let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_thms_5003_);
        crate::leanh::lean_dec_ref(v_monad_5001_);
        v___x_5036_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9);
        v___x_5037_ = l_Lean_MessageData_ofExpr(v_e_5002_);
        v___x_5038_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5038_, 0, v___x_5036_);
        crate::leanh::lean_ctor_set(v___x_5038_, 1, v___x_5037_);
        v___x_5039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7);
        v___x_5040_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5040_, 0, v___x_5038_);
        crate::leanh::lean_ctor_set(v___x_5040_, 1, v___x_5039_);
        v___x_5041_ =
            l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(
                v___x_5040_,
                v___y_5011_,
                v___y_5012_,
                v___y_5013_,
                v___y_5014_,
            );
        return v___x_5041_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___boxed(
    mut v___x_5042_: *mut crate::leanh::LeanObject,
    mut v_monad_5043_: *mut crate::leanh::LeanObject,
    mut v_e_5044_: *mut crate::leanh::LeanObject,
    mut v_thms_5045_: *mut crate::leanh::LeanObject,
    mut v___y_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
    mut v___y_5056_: *mut crate::leanh::LeanObject,
    mut v___y_5057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_79070__boxed_5058_: u8 = 0;
    let mut v_res_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_79070__boxed_5058_ = (crate::leanh::lean_unbox(v___x_5042_) as u8);
    v_res_5059_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1(v___x_79070__boxed_5058_, v_monad_5043_, v_e_5044_, v_thms_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
    crate::leanh::lean_dec(v___y_5056_);
    crate::leanh::lean_dec_ref(v___y_5055_);
    crate::leanh::lean_dec(v___y_5054_);
    crate::leanh::lean_dec_ref(v___y_5053_);
    crate::leanh::lean_dec(v___y_5052_);
    crate::leanh::lean_dec_ref(v___y_5051_);
    crate::leanh::lean_dec(v___y_5050_);
    crate::leanh::lean_dec_ref(v___y_5049_);
    crate::leanh::lean_dec(v___y_5048_);
    crate::leanh::lean_dec(v___y_5047_);
    crate::leanh::lean_dec_ref(v___y_5046_);
    return v_res_5059_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(
    mut v_goal_5060_: *mut crate::leanh::LeanObject,
    mut v___x_5061_: *mut crate::leanh::LeanObject,
    mut v_target_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
    mut v___y_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5083_: u8 = 0;
    let mut v_unused_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5075_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(
                    v_goal_5060_,
                    v___y_5063_,
                    v___y_5064_,
                    v___y_5065_,
                    v___y_5066_,
                    v___y_5067_,
                    v___y_5068_,
                    v___y_5069_,
                    v___y_5070_,
                    v___y_5071_,
                    v___y_5072_,
                    v___y_5073_,
                );
                if crate::leanh::lean_obj_tag(v___x_5075_) == 0 {
                    v_isSharedCheck_5083_ = (!crate::leanh::lean_is_exclusive(v___x_5075_)) as u8;
                    if v_isSharedCheck_5083_ == 0 {
                        v_unused_5084_ = crate::leanh::lean_ctor_get(v___x_5075_, 0);
                        crate::leanh::lean_dec(v_unused_5084_);
                        v___x_5077_ = v___x_5075_;
                        v_isShared_5078_ = v_isSharedCheck_5083_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5075_);
                        v___x_5077_ = crate::leanh::lean_box(0);
                        v_isShared_5078_ = v_isSharedCheck_5083_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5061_);
                    v_a_5085_ = crate::leanh::lean_ctor_get(v___x_5075_, 0);
                    v_isSharedCheck_5092_ = (!crate::leanh::lean_is_exclusive(v___x_5075_)) as u8;
                    if v_isSharedCheck_5092_ == 0 {
                        v___x_5087_ = v___x_5075_;
                        v_isShared_5088_ = v_isSharedCheck_5092_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5085_);
                        crate::leanh::lean_dec(v___x_5075_);
                        v___x_5087_ = crate::leanh::lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5092_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5079_, 0, v___x_5061_);
                if v_isShared_5078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5077_, 0, v___x_5079_);
                    v___x_5081_ = v___x_5077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5079_);
                    v___x_5081_ = v_reuseFailAlloc_5082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5081_;
            }
            3 => {
                if v_isShared_5088_ == 0 {
                    v___x_5090_ = v___x_5087_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
                    v___x_5090_ = v_reuseFailAlloc_5091_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0___boxed(
    mut v_goal_5093_: *mut crate::leanh::LeanObject,
    mut v___x_5094_: *mut crate::leanh::LeanObject,
    mut v_target_5095_: *mut crate::leanh::LeanObject,
    mut v___y_5096_: *mut crate::leanh::LeanObject,
    mut v___y_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
    mut v___y_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5108_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(v_goal_5093_, v___x_5094_, v_target_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
    crate::leanh::lean_dec(v___y_5106_);
    crate::leanh::lean_dec_ref(v___y_5105_);
    crate::leanh::lean_dec(v___y_5104_);
    crate::leanh::lean_dec_ref(v___y_5103_);
    crate::leanh::lean_dec(v___y_5102_);
    crate::leanh::lean_dec_ref(v___y_5101_);
    crate::leanh::lean_dec(v___y_5100_);
    crate::leanh::lean_dec_ref(v___y_5099_);
    crate::leanh::lean_dec(v___y_5098_);
    crate::leanh::lean_dec(v___y_5097_);
    crate::leanh::lean_dec_ref(v___y_5096_);
    crate::leanh::lean_dec_ref(v_target_5095_);
    return v_res_5108_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5110_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0;
    v___x_5111_ = l_Lean_stringToMessageData(v___x_5110_);
    return v___x_5111_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(
    mut v_a_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5130_: u8 = 0;
    let mut v_a_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5137_: u8 = 0;
    let mut v_a_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5141_: u8 = 0;
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5145_: u8 = 0;
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: u8 = 0;
    let mut v_mvarId_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5163_: u8 = 0;
    let mut v_e_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5175_: u8 = 0;
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5179_: u8 = 0;
    let mut v_reuseFailAlloc_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut v_unused_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorOnMissingSpec_5184_: u8 = 0;
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut v_e_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_monad_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: u8 = 0;
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5208_: u8 = 0;
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5212_: u8 = 0;
    let mut v_scope_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: u8 = 0;
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTac_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5231_: u8 = 0;
    let mut v_a_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5235_: u8 = 0;
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5239_: u8 = 0;
    let mut v_target_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5245_: u8 = 0;
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5249_: u8 = 0;
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5255_: u8 = 0;
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5259_: u8 = 0;
    let mut v_a_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5263_: u8 = 0;
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5146_ = lean_array_get_size(v_a_5112_);
                v___x_5147_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5148_ = lean_nat_sub(v___x_5146_, v___x_5147_);
                v___x_5149_ = lean_nat_dec_lt(v___x_5148_, v___x_5146_);
                if v___x_5149_ == 0 {
                    crate::leanh::lean_dec(v___x_5148_);
                    v___x_5150_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5150_, 0, v_a_5112_);
                    return v___x_5150_;
                } else {
                    v___x_5151_ =
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_5114_);
                    if crate::leanh::lean_obj_tag(v___x_5151_) == 0 {
                        v_a_5152_ = crate::leanh::lean_ctor_get(v___x_5151_, 0);
                        crate::leanh::lean_inc(v_a_5152_);
                        crate::leanh::lean_dec_ref_known(v___x_5151_, 1);
                        v___x_5153_ = lean_array_fget_borrowed(v_a_5112_, v___x_5148_);
                        crate::leanh::lean_dec(v___x_5148_);
                        v_goal_5154_ = crate::leanh::lean_ctor_get(v___x_5153_, 0);
                        crate::leanh::lean_inc_ref(v_goal_5154_);
                        v_scope_5155_ = crate::leanh::lean_ctor_get(v___x_5153_, 1);
                        crate::leanh::lean_inc_ref(v_scope_5155_);
                        v___x_5156_ = lean_array_pop(v_a_5112_);
                        v___x_5157_ = (crate::leanh::lean_unbox(v_a_5152_) as u8);
                        crate::leanh::lean_dec(v_a_5152_);
                        if v___x_5157_ == 0 {
                            v_mvarId_5158_ = crate::leanh::lean_ctor_get(v_goal_5154_, 1);
                            crate::leanh::lean_inc(v_mvarId_5158_);
                            v___x_5159_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(
                                v_scope_5155_,
                                v_mvarId_5158_,
                                v___y_5113_,
                                v___y_5114_,
                                v___y_5115_,
                                v___y_5116_,
                                v___y_5117_,
                                v___y_5118_,
                                v___y_5119_,
                                v___y_5120_,
                                v___y_5121_,
                                v___y_5122_,
                                v___y_5123_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5159_) == 0 {
                                v_a_5160_ = crate::leanh::lean_ctor_get(v___x_5159_, 0);
                                crate::leanh::lean_inc(v_a_5160_);
                                crate::leanh::lean_dec_ref_known(v___x_5159_, 1);
                                match crate::leanh::lean_obj_tag(v_a_5160_) {
                                    2 => {
                                        crate::leanh::lean_inc(v_mvarId_5158_);
                                        v_isSharedCheck_5181_ =
                                            (!crate::leanh::lean_is_exclusive(v_goal_5154_)) as u8;
                                        if v_isSharedCheck_5181_ == 0 {
                                            v_unused_5182_ =
                                                crate::leanh::lean_ctor_get(v_goal_5154_, 1);
                                            crate::leanh::lean_dec(v_unused_5182_);
                                            v_unused_5183_ =
                                                crate::leanh::lean_ctor_get(v_goal_5154_, 0);
                                            crate::leanh::lean_dec(v_unused_5183_);
                                            v___x_5162_ = v_goal_5154_;
                                            v_isShared_5163_ = v_isSharedCheck_5181_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_goal_5154_);
                                            v___x_5162_ = crate::leanh::lean_box(0);
                                            v_isShared_5163_ = v_isSharedCheck_5181_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                    3 => {
                                        v_errorOnMissingSpec_5184_ =
                                            crate::leanh::lean_ctor_get_uint8(
                                                v___y_5113_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 19
                                                    + 2)
                                                    as u32,
                                            );
                                        if v_errorOnMissingSpec_5184_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v_a_5160_, 3);
                                            v___x_5185_ =
                                                l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(
                                                    v_goal_5154_,
                                                    v___y_5113_,
                                                    v___y_5114_,
                                                    v___y_5115_,
                                                    v___y_5116_,
                                                    v___y_5117_,
                                                    v___y_5118_,
                                                    v___y_5119_,
                                                    v___y_5120_,
                                                    v___y_5121_,
                                                    v___y_5122_,
                                                    v___y_5123_,
                                                );
                                            if crate::leanh::lean_obj_tag(v___x_5185_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_5185_, 1);
                                                v_a_5112_ = v___x_5156_;
                                                state = 0;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_5156_);
                                                v_a_5187_ =
                                                    crate::leanh::lean_ctor_get(v___x_5185_, 0);
                                                v_isSharedCheck_5194_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5185_))
                                                        as u8;
                                                if v_isSharedCheck_5194_ == 0 {
                                                    v___x_5189_ = v___x_5185_;
                                                    v_isShared_5190_ = v_isSharedCheck_5194_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5187_);
                                                    crate::leanh::lean_dec(v___x_5185_);
                                                    v___x_5189_ = crate::leanh::lean_box(0);
                                                    v_isShared_5190_ = v_isSharedCheck_5194_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_inc(v_mvarId_5158_);
                                            crate::leanh::lean_dec_ref(v_goal_5154_);
                                            v_e_5195_ = crate::leanh::lean_ctor_get(v_a_5160_, 0);
                                            crate::leanh::lean_inc_ref(v_e_5195_);
                                            v_monad_5196_ =
                                                crate::leanh::lean_ctor_get(v_a_5160_, 1);
                                            crate::leanh::lean_inc_ref(v_monad_5196_);
                                            v_thms_5197_ =
                                                crate::leanh::lean_ctor_get(v_a_5160_, 2);
                                            crate::leanh::lean_inc_ref(v_thms_5197_);
                                            crate::leanh::lean_dec_ref_known(v_a_5160_, 3);
                                            v___x_5198_ = lean_array_get_size(v_thms_5197_);
                                            v___x_5199_ = crate::leanh::lean_unsigned_to_nat(0);
                                            v___x_5200_ = lean_nat_dec_eq(v___x_5198_, v___x_5199_);
                                            v___x_5201_ =
                                                crate::leanh::lean_box((v___x_5200_) as usize);
                                            v___y_5202_ = crate::leanh::lean_alloc_closure(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___boxed as *mut core::ffi::c_void, 16, 4);
                                            crate::leanh::lean_closure_set(
                                                v___y_5202_,
                                                0,
                                                v___x_5201_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___y_5202_,
                                                1,
                                                v_monad_5196_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___y_5202_,
                                                2,
                                                v_e_5195_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___y_5202_,
                                                3,
                                                v_thms_5197_,
                                            );
                                            v___x_5203_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_5158_, v___y_5202_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
                                            if crate::leanh::lean_obj_tag(v___x_5203_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_5203_, 1);
                                                v_a_5112_ = v___x_5156_;
                                                state = 0;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_5156_);
                                                v_a_5205_ =
                                                    crate::leanh::lean_ctor_get(v___x_5203_, 0);
                                                v_isSharedCheck_5212_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5203_))
                                                        as u8;
                                                if v_isSharedCheck_5212_ == 0 {
                                                    v___x_5207_ = v___x_5203_;
                                                    v_isShared_5208_ = v_isSharedCheck_5212_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5205_);
                                                    crate::leanh::lean_dec(v___x_5203_);
                                                    v___x_5207_ = crate::leanh::lean_box(0);
                                                    v_isShared_5208_ = v_isSharedCheck_5212_;
                                                    state = 12;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                    4 => {
                                        v_scope_5213_ = crate::leanh::lean_ctor_get(v_a_5160_, 0);
                                        crate::leanh::lean_inc_ref(v_scope_5213_);
                                        v_subgoals_5214_ =
                                            crate::leanh::lean_ctor_get(v_a_5160_, 1);
                                        crate::leanh::lean_inc(v_subgoals_5214_);
                                        crate::leanh::lean_dec_ref_known(v_a_5160_, 2);
                                        v___x_5215_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_5214_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
                                        crate::leanh::lean_dec(v_subgoals_5214_);
                                        if crate::leanh::lean_obj_tag(v___x_5215_) == 0 {
                                            v_a_5216_ = crate::leanh::lean_ctor_get(v___x_5215_, 0);
                                            crate::leanh::lean_inc(v_a_5216_);
                                            crate::leanh::lean_dec_ref_known(v___x_5215_, 1);
                                            v___x_5217_ = lean_array_get_size(v_a_5216_);
                                            v___x_5218_ = lean_nat_dec_lt(v___x_5147_, v___x_5217_);
                                            if v___x_5218_ == 0 {
                                                v___x_5219_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_5216_, v_scope_5213_, v___x_5156_, v_goal_5154_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
                                                crate::leanh::lean_dec_ref(v_goal_5154_);
                                                v___y_5126_ = v___x_5219_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v_preTac_5220_ =
                                                    crate::leanh::lean_ctor_get(v___y_5113_, 17);
                                                v___x_5221_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(v_preTac_5220_, v_goal_5154_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
                                                if crate::leanh::lean_obj_tag(v___x_5221_) == 0 {
                                                    v_a_5222_ =
                                                        crate::leanh::lean_ctor_get(v___x_5221_, 0);
                                                    crate::leanh::lean_inc(v_a_5222_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_5221_,
                                                        1,
                                                    );
                                                    v___x_5223_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_5216_, v_scope_5213_, v___x_5156_, v_a_5222_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
                                                    crate::leanh::lean_dec(v_a_5222_);
                                                    v___y_5126_ = v___x_5223_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_a_5216_);
                                                    crate::leanh::lean_dec_ref(v_scope_5213_);
                                                    crate::leanh::lean_dec_ref(v___x_5156_);
                                                    v_a_5224_ =
                                                        crate::leanh::lean_ctor_get(v___x_5221_, 0);
                                                    v_isSharedCheck_5231_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5221_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5231_ == 0 {
                                                        v___x_5226_ = v___x_5221_;
                                                        v_isShared_5227_ = v_isSharedCheck_5231_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5224_);
                                                        crate::leanh::lean_dec(v___x_5221_);
                                                        v___x_5226_ = crate::leanh::lean_box(0);
                                                        v_isShared_5227_ = v_isSharedCheck_5231_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_scope_5213_);
                                            crate::leanh::lean_dec_ref(v___x_5156_);
                                            crate::leanh::lean_dec_ref(v_goal_5154_);
                                            v_a_5232_ = crate::leanh::lean_ctor_get(v___x_5215_, 0);
                                            v_isSharedCheck_5239_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5215_))
                                                    as u8;
                                            if v_isSharedCheck_5239_ == 0 {
                                                v___x_5234_ = v___x_5215_;
                                                v_isShared_5235_ = v_isSharedCheck_5239_;
                                                state = 16;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5232_);
                                                crate::leanh::lean_dec(v___x_5215_);
                                                v___x_5234_ = crate::leanh::lean_box(0);
                                                v_isShared_5235_ = v_isSharedCheck_5239_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                    _ => {
                                        v_target_5240_ = crate::leanh::lean_ctor_get(v_a_5160_, 0);
                                        crate::leanh::lean_inc_ref(v_target_5240_);
                                        crate::leanh::lean_dec(v_a_5160_);
                                        v___x_5241_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(v_goal_5154_, v___x_5156_, v_target_5240_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
                                        crate::leanh::lean_dec_ref(v_target_5240_);
                                        v___y_5126_ = v___x_5241_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5156_);
                                crate::leanh::lean_dec_ref(v_goal_5154_);
                                v_a_5242_ = crate::leanh::lean_ctor_get(v___x_5159_, 0);
                                v_isSharedCheck_5249_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5159_)) as u8;
                                if v_isSharedCheck_5249_ == 0 {
                                    v___x_5244_ = v___x_5159_;
                                    v_isShared_5245_ = v_isSharedCheck_5249_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5242_);
                                    crate::leanh::lean_dec(v___x_5159_);
                                    v___x_5244_ = crate::leanh::lean_box(0);
                                    v_isShared_5245_ = v_isSharedCheck_5249_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_scope_5155_);
                            v___x_5250_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(
                                v_goal_5154_,
                                v___y_5113_,
                                v___y_5114_,
                                v___y_5115_,
                                v___y_5116_,
                                v___y_5117_,
                                v___y_5118_,
                                v___y_5119_,
                                v___y_5120_,
                                v___y_5121_,
                                v___y_5122_,
                                v___y_5123_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5250_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5250_, 1);
                                v_a_5112_ = v___x_5156_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5156_);
                                v_a_5252_ = crate::leanh::lean_ctor_get(v___x_5250_, 0);
                                v_isSharedCheck_5259_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5250_)) as u8;
                                if v_isSharedCheck_5259_ == 0 {
                                    v___x_5254_ = v___x_5250_;
                                    v_isShared_5255_ = v_isSharedCheck_5259_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5252_);
                                    crate::leanh::lean_dec(v___x_5250_);
                                    v___x_5254_ = crate::leanh::lean_box(0);
                                    v_isShared_5255_ = v_isSharedCheck_5259_;
                                    state = 20;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5148_);
                        crate::leanh::lean_dec_ref(v_a_5112_);
                        v_a_5260_ = crate::leanh::lean_ctor_get(v___x_5151_, 0);
                        v_isSharedCheck_5267_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5151_)) as u8;
                        if v_isSharedCheck_5267_ == 0 {
                            v___x_5262_ = v___x_5151_;
                            v_isShared_5263_ = v_isSharedCheck_5267_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5260_);
                            crate::leanh::lean_dec(v___x_5151_);
                            v___x_5262_ = crate::leanh::lean_box(0);
                            v_isShared_5263_ = v_isSharedCheck_5267_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5126_) == 0 {
                    v_a_5127_ = crate::leanh::lean_ctor_get(v___y_5126_, 0);
                    v_isSharedCheck_5137_ = (!crate::leanh::lean_is_exclusive(v___y_5126_)) as u8;
                    if v_isSharedCheck_5137_ == 0 {
                        v___x_5129_ = v___y_5126_;
                        v_isShared_5130_ = v_isSharedCheck_5137_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5127_);
                        crate::leanh::lean_dec(v___y_5126_);
                        v___x_5129_ = crate::leanh::lean_box(0);
                        v_isShared_5130_ = v_isSharedCheck_5137_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5138_ = crate::leanh::lean_ctor_get(v___y_5126_, 0);
                    v_isSharedCheck_5145_ = (!crate::leanh::lean_is_exclusive(v___y_5126_)) as u8;
                    if v_isSharedCheck_5145_ == 0 {
                        v___x_5140_ = v___y_5126_;
                        v_isShared_5141_ = v_isSharedCheck_5145_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5138_);
                        crate::leanh::lean_dec(v___y_5126_);
                        v___x_5140_ = crate::leanh::lean_box(0);
                        v_isShared_5141_ = v_isSharedCheck_5145_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5127_) == 0 {
                    v_a_5131_ = crate::leanh::lean_ctor_get(v_a_5127_, 0);
                    crate::leanh::lean_inc(v_a_5131_);
                    crate::leanh::lean_dec_ref_known(v_a_5127_, 1);
                    if v_isShared_5130_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5129_, 0, v_a_5131_);
                        v___x_5133_ = v___x_5129_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5131_);
                        v___x_5133_ = v_reuseFailAlloc_5134_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5129_);
                    v_a_5135_ = crate::leanh::lean_ctor_get(v_a_5127_, 0);
                    crate::leanh::lean_inc(v_a_5135_);
                    crate::leanh::lean_dec_ref_known(v_a_5127_, 1);
                    v_a_5112_ = v_a_5135_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_5133_;
            }
            4 => {
                if v_isShared_5141_ == 0 {
                    v___x_5143_ = v___x_5140_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
                    v___x_5143_ = v_reuseFailAlloc_5144_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5143_;
            }
            6 => {
                v_e_5164_ = crate::leanh::lean_ctor_get(v_a_5160_, 0);
                crate::leanh::lean_inc_ref(v_e_5164_);
                crate::leanh::lean_dec_ref_known(v_a_5160_, 1);
                v___x_5165_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1);
                v___x_5166_ = l_Lean_MessageData_ofExpr(v_e_5164_);
                if v_isShared_5163_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5162_, 7);
                    crate::leanh::lean_ctor_set(v___x_5162_, 1, v___x_5166_);
                    crate::leanh::lean_ctor_set(v___x_5162_, 0, v___x_5165_);
                    v___x_5168_ = v___x_5162_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5180_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 1, v___x_5166_);
                    v___x_5168_ = v_reuseFailAlloc_5180_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5169_ = crate::leanh::lean_alloc_closure(l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed as *mut core::ffi::c_void, 14, 2);
                crate::leanh::lean_closure_set(v___x_5169_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5169_, 1, v___x_5168_);
                v___x_5170_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_5158_, v___x_5169_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_);
                if crate::leanh::lean_obj_tag(v___x_5170_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5170_, 1);
                    v_a_5112_ = v___x_5156_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5156_);
                    v_a_5172_ = crate::leanh::lean_ctor_get(v___x_5170_, 0);
                    v_isSharedCheck_5179_ = (!crate::leanh::lean_is_exclusive(v___x_5170_)) as u8;
                    if v_isSharedCheck_5179_ == 0 {
                        v___x_5174_ = v___x_5170_;
                        v_isShared_5175_ = v_isSharedCheck_5179_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5172_);
                        crate::leanh::lean_dec(v___x_5170_);
                        v___x_5174_ = crate::leanh::lean_box(0);
                        v_isShared_5175_ = v_isSharedCheck_5179_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5175_ == 0 {
                    v___x_5177_ = v___x_5174_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
                    v___x_5177_ = v_reuseFailAlloc_5178_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5177_;
            }
            10 => {
                if v_isShared_5190_ == 0 {
                    v___x_5192_ = v___x_5189_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5192_;
            }
            12 => {
                if v_isShared_5208_ == 0 {
                    v___x_5210_ = v___x_5207_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
                    v___x_5210_ = v_reuseFailAlloc_5211_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5210_;
            }
            14 => {
                if v_isShared_5227_ == 0 {
                    v___x_5229_ = v___x_5226_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
                    v___x_5229_ = v_reuseFailAlloc_5230_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5229_;
            }
            16 => {
                if v_isShared_5235_ == 0 {
                    v___x_5237_ = v___x_5234_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_a_5232_);
                    v___x_5237_ = v_reuseFailAlloc_5238_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5237_;
            }
            18 => {
                if v_isShared_5245_ == 0 {
                    v___x_5247_ = v___x_5244_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
                    v___x_5247_ = v_reuseFailAlloc_5248_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5247_;
            }
            20 => {
                if v_isShared_5255_ == 0 {
                    v___x_5257_ = v___x_5254_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_a_5252_);
                    v___x_5257_ = v_reuseFailAlloc_5258_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5257_;
            }
            22 => {
                if v_isShared_5263_ == 0 {
                    v___x_5265_ = v___x_5262_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5266_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
                    v___x_5265_ = v_reuseFailAlloc_5266_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___boxed(
    mut v_a_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
    mut v___y_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
    mut v___y_5273_: *mut crate::leanh::LeanObject,
    mut v___y_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5281_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v_a_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
    crate::leanh::lean_dec(v___y_5279_);
    crate::leanh::lean_dec_ref(v___y_5278_);
    crate::leanh::lean_dec(v___y_5277_);
    crate::leanh::lean_dec_ref(v___y_5276_);
    crate::leanh::lean_dec(v___y_5275_);
    crate::leanh::lean_dec_ref(v___y_5274_);
    crate::leanh::lean_dec(v___y_5273_);
    crate::leanh::lean_dec_ref(v___y_5272_);
    crate::leanh::lean_dec(v___y_5271_);
    crate::leanh::lean_dec(v___y_5270_);
    crate::leanh::lean_dec_ref(v___y_5269_);
    return v_res_5281_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_work(
    mut v_scope_5282_: *mut crate::leanh::LeanObject,
    mut v_goal_5283_: *mut crate::leanh::LeanObject,
    mut v_a_5284_: *mut crate::leanh::LeanObject,
    mut v_a_5285_: *mut crate::leanh::LeanObject,
    mut v_a_5286_: *mut crate::leanh::LeanObject,
    mut v_a_5287_: *mut crate::leanh::LeanObject,
    mut v_a_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
    mut v_a_5293_: *mut crate::leanh::LeanObject,
    mut v_a_5294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5300_: u8 = 0;
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_unused_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut v_reuseFailAlloc_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5331_: u8 = 0;
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5335_: u8 = 0;
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_5296_ = crate::leanh::lean_ctor_get(v_goal_5283_, 0);
                v_mvarId_5297_ = crate::leanh::lean_ctor_get(v_goal_5283_, 1);
                v_isSharedCheck_5336_ = (!crate::leanh::lean_is_exclusive(v_goal_5283_)) as u8;
                if v_isSharedCheck_5336_ == 0 {
                    v___x_5299_ = v_goal_5283_;
                    v_isShared_5300_ = v_isSharedCheck_5336_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_5297_);
                    crate::leanh::lean_inc(v_toGoalState_5296_);
                    crate::leanh::lean_dec(v_goal_5283_);
                    v___x_5299_ = crate::leanh::lean_box(0);
                    v_isShared_5300_ = v_isSharedCheck_5336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5301_ = l_Lean_Meta_Sym_preprocessMVar(
                    v_mvarId_5297_,
                    v_a_5289_,
                    v_a_5290_,
                    v_a_5291_,
                    v_a_5292_,
                    v_a_5293_,
                    v_a_5294_,
                );
                if crate::leanh::lean_obj_tag(v___x_5301_) == 0 {
                    v_a_5302_ = crate::leanh::lean_ctor_get(v___x_5301_, 0);
                    crate::leanh::lean_inc(v_a_5302_);
                    crate::leanh::lean_dec_ref_known(v___x_5301_, 1);
                    if v_isShared_5300_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5299_, 1, v_a_5302_);
                        v___x_5304_ = v___x_5299_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_toGoalState_5296_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_a_5302_);
                        v___x_5304_ = v_reuseFailAlloc_5327_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5299_);
                    crate::leanh::lean_dec_ref(v_toGoalState_5296_);
                    crate::leanh::lean_dec_ref(v_scope_5282_);
                    v_a_5328_ = crate::leanh::lean_ctor_get(v___x_5301_, 0);
                    v_isSharedCheck_5335_ = (!crate::leanh::lean_is_exclusive(v___x_5301_)) as u8;
                    if v_isSharedCheck_5335_ == 0 {
                        v___x_5330_ = v___x_5301_;
                        v_isShared_5331_ = v_isSharedCheck_5335_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5328_);
                        crate::leanh::lean_dec(v___x_5301_);
                        v___x_5330_ = crate::leanh::lean_box(0);
                        v_isShared_5331_ = v_isSharedCheck_5335_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5305_, 0, v___x_5304_);
                crate::leanh::lean_ctor_set(v___x_5305_, 1, v_scope_5282_);
                v___x_5306_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5307_ = lean_mk_empty_array_with_capacity(v___x_5306_);
                v___x_5308_ = lean_array_push(v___x_5307_, v___x_5305_);
                v___x_5309_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v___x_5308_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_);
                if crate::leanh::lean_obj_tag(v___x_5309_) == 0 {
                    v_isSharedCheck_5317_ = (!crate::leanh::lean_is_exclusive(v___x_5309_)) as u8;
                    if v_isSharedCheck_5317_ == 0 {
                        v_unused_5318_ = crate::leanh::lean_ctor_get(v___x_5309_, 0);
                        crate::leanh::lean_dec(v_unused_5318_);
                        v___x_5311_ = v___x_5309_;
                        v_isShared_5312_ = v_isSharedCheck_5317_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5309_);
                        v___x_5311_ = crate::leanh::lean_box(0);
                        v_isShared_5312_ = v_isSharedCheck_5317_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5319_ = crate::leanh::lean_ctor_get(v___x_5309_, 0);
                    v_isSharedCheck_5326_ = (!crate::leanh::lean_is_exclusive(v___x_5309_)) as u8;
                    if v_isSharedCheck_5326_ == 0 {
                        v___x_5321_ = v___x_5309_;
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5319_);
                        crate::leanh::lean_dec(v___x_5309_);
                        v___x_5321_ = crate::leanh::lean_box(0);
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5313_ = crate::leanh::lean_box(0);
                if v_isShared_5312_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5311_, 0, v___x_5313_);
                    v___x_5315_ = v___x_5311_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5315_;
            }
            5 => {
                if v_isShared_5322_ == 0 {
                    v___x_5324_ = v___x_5321_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5324_;
            }
            7 => {
                if v_isShared_5331_ == 0 {
                    v___x_5333_ = v___x_5330_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5328_);
                    v___x_5333_ = v_reuseFailAlloc_5334_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(
    mut v_scope_5337_: *mut crate::leanh::LeanObject,
    mut v_goal_5338_: *mut crate::leanh::LeanObject,
    mut v_a_5339_: *mut crate::leanh::LeanObject,
    mut v_a_5340_: *mut crate::leanh::LeanObject,
    mut v_a_5341_: *mut crate::leanh::LeanObject,
    mut v_a_5342_: *mut crate::leanh::LeanObject,
    mut v_a_5343_: *mut crate::leanh::LeanObject,
    mut v_a_5344_: *mut crate::leanh::LeanObject,
    mut v_a_5345_: *mut crate::leanh::LeanObject,
    mut v_a_5346_: *mut crate::leanh::LeanObject,
    mut v_a_5347_: *mut crate::leanh::LeanObject,
    mut v_a_5348_: *mut crate::leanh::LeanObject,
    mut v_a_5349_: *mut crate::leanh::LeanObject,
    mut v_a_5350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5351_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(
        v_scope_5337_,
        v_goal_5338_,
        v_a_5339_,
        v_a_5340_,
        v_a_5341_,
        v_a_5342_,
        v_a_5343_,
        v_a_5344_,
        v_a_5345_,
        v_a_5346_,
        v_a_5347_,
        v_a_5348_,
        v_a_5349_,
    );
    crate::leanh::lean_dec(v_a_5349_);
    crate::leanh::lean_dec_ref(v_a_5348_);
    crate::leanh::lean_dec(v_a_5347_);
    crate::leanh::lean_dec_ref(v_a_5346_);
    crate::leanh::lean_dec(v_a_5345_);
    crate::leanh::lean_dec_ref(v_a_5344_);
    crate::leanh::lean_dec(v_a_5343_);
    crate::leanh::lean_dec_ref(v_a_5342_);
    crate::leanh::lean_dec(v_a_5341_);
    crate::leanh::lean_dec(v_a_5340_);
    crate::leanh::lean_dec_ref(v_a_5339_);
    return v_res_5351_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(
    mut v_inst_5352_: *mut crate::leanh::LeanObject,
    mut v_a_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
    mut v___y_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5366_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v_a_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
    return v___x_5366_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___boxed(
    mut v_inst_5367_: *mut crate::leanh::LeanObject,
    mut v_a_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
    mut v___y_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5381_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(v_inst_5367_, v_a_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
    crate::leanh::lean_dec(v___y_5379_);
    crate::leanh::lean_dec_ref(v___y_5378_);
    crate::leanh::lean_dec(v___y_5377_);
    crate::leanh::lean_dec_ref(v___y_5376_);
    crate::leanh::lean_dec(v___y_5375_);
    crate::leanh::lean_dec_ref(v___y_5374_);
    crate::leanh::lean_dec(v___y_5373_);
    crate::leanh::lean_dec_ref(v___y_5372_);
    crate::leanh::lean_dec(v___y_5371_);
    crate::leanh::lean_dec(v___y_5370_);
    crate::leanh::lean_dec_ref(v___y_5369_);
    return v_res_5381_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(
    mut v_as_5383_: *mut crate::leanh::LeanObject,
    mut v_i_5384_: *mut crate::leanh::LeanObject,
    mut v_j_5385_: *mut crate::leanh::LeanObject,
    mut v_bs_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
    mut v___y_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5393_: u8 = 0;
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v_a_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5392_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5393_ = lean_nat_dec_eq(v_i_5384_, v_zero_5392_);
                if v_isZero_5393_ == 1 {
                    crate::leanh::lean_dec(v_j_5385_);
                    crate::leanh::lean_dec(v_i_5384_);
                    v___x_5394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5394_, 0, v_bs_5386_);
                    return v___x_5394_;
                } else {
                    v___x_5395_ = lean_array_fget_borrowed(v_as_5383_, v_j_5385_);
                    v_mvarId_5396_ = crate::leanh::lean_ctor_get(v___x_5395_, 1);
                    crate::leanh::lean_inc(v_mvarId_5396_);
                    v___x_5397_ = l_Lean_MVarId_getTag(
                        v_mvarId_5396_,
                        v___y_5387_,
                        v___y_5388_,
                        v___y_5389_,
                        v___y_5390_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5397_) == 0 {
                        v_a_5398_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                        crate::leanh::lean_inc(v_a_5398_);
                        crate::leanh::lean_dec_ref_known(v___x_5397_, 1);
                        v___x_5399_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0;
                        v___x_5400_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5401_ = lean_nat_add(v_j_5385_, v___x_5400_);
                        crate::leanh::lean_dec(v_j_5385_);
                        crate::leanh::lean_inc(v___x_5401_);
                        v___x_5402_ = l_Nat_reprFast(v___x_5401_);
                        v___x_5403_ = lean_string_append(v___x_5399_, v___x_5402_);
                        crate::leanh::lean_dec_ref(v___x_5402_);
                        v___x_5404_ = crate::leanh::lean_box(0);
                        v___x_5405_ = l_Lean_Name_str___override(v___x_5404_, v___x_5403_);
                        v___x_5406_ = lean_erase_macro_scopes(v_a_5398_);
                        v___x_5407_ = l_Lean_Name_append(v___x_5405_, v___x_5406_);
                        crate::leanh::lean_inc(v_mvarId_5396_);
                        v___x_5408_ =
                            l_Lean_MVarId_setTag___redArg(v_mvarId_5396_, v___x_5407_, v___y_5388_);
                        if crate::leanh::lean_obj_tag(v___x_5408_) == 0 {
                            v_a_5409_ = crate::leanh::lean_ctor_get(v___x_5408_, 0);
                            crate::leanh::lean_inc(v_a_5409_);
                            crate::leanh::lean_dec_ref_known(v___x_5408_, 1);
                            v_n_5410_ = lean_nat_sub(v_i_5384_, v___x_5400_);
                            crate::leanh::lean_dec(v_i_5384_);
                            v___x_5411_ = lean_array_push(v_bs_5386_, v_a_5409_);
                            v_i_5384_ = v_n_5410_;
                            v_j_5385_ = v___x_5401_;
                            v_bs_5386_ = v___x_5411_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5401_);
                            crate::leanh::lean_dec_ref(v_bs_5386_);
                            crate::leanh::lean_dec(v_i_5384_);
                            v_a_5413_ = crate::leanh::lean_ctor_get(v___x_5408_, 0);
                            v_isSharedCheck_5420_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5408_)) as u8;
                            if v_isSharedCheck_5420_ == 0 {
                                v___x_5415_ = v___x_5408_;
                                v_isShared_5416_ = v_isSharedCheck_5420_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5413_);
                                crate::leanh::lean_dec(v___x_5408_);
                                v___x_5415_ = crate::leanh::lean_box(0);
                                v_isShared_5416_ = v_isSharedCheck_5420_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5386_);
                        crate::leanh::lean_dec(v_j_5385_);
                        crate::leanh::lean_dec(v_i_5384_);
                        v_a_5421_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                        v_isSharedCheck_5428_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5397_)) as u8;
                        if v_isSharedCheck_5428_ == 0 {
                            v___x_5423_ = v___x_5397_;
                            v_isShared_5424_ = v_isSharedCheck_5428_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5421_);
                            crate::leanh::lean_dec(v___x_5397_);
                            v___x_5423_ = crate::leanh::lean_box(0);
                            v_isShared_5424_ = v_isSharedCheck_5428_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5416_ == 0 {
                    v___x_5418_ = v___x_5415_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
                    v___x_5418_ = v_reuseFailAlloc_5419_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5418_;
            }
            3 => {
                if v_isShared_5424_ == 0 {
                    v___x_5426_ = v___x_5423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
                    v___x_5426_ = v_reuseFailAlloc_5427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___boxed(
    mut v_as_5429_: *mut crate::leanh::LeanObject,
    mut v_i_5430_: *mut crate::leanh::LeanObject,
    mut v_j_5431_: *mut crate::leanh::LeanObject,
    mut v_bs_5432_: *mut crate::leanh::LeanObject,
    mut v___y_5433_: *mut crate::leanh::LeanObject,
    mut v___y_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
    mut v___y_5437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5438_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(
            v_as_5429_,
            v_i_5430_,
            v_j_5431_,
            v_bs_5432_,
            v___y_5433_,
            v___y_5434_,
            v___y_5435_,
            v___y_5436_,
        );
    crate::leanh::lean_dec(v___y_5436_);
    crate::leanh::lean_dec_ref(v___y_5435_);
    crate::leanh::lean_dec(v___y_5434_);
    crate::leanh::lean_dec_ref(v___y_5433_);
    crate::leanh::lean_dec_ref(v_as_5429_);
    return v_res_5438_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(
    mut v_as_5440_: *mut crate::leanh::LeanObject,
    mut v_i_5441_: *mut crate::leanh::LeanObject,
    mut v_j_5442_: *mut crate::leanh::LeanObject,
    mut v_bs_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5447_: u8 = 0;
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5465_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5446_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5447_ = lean_nat_dec_eq(v_i_5441_, v_zero_5446_);
                if v_isZero_5447_ == 1 {
                    crate::leanh::lean_dec(v_j_5442_);
                    crate::leanh::lean_dec(v_i_5441_);
                    v___x_5448_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5448_, 0, v_bs_5443_);
                    return v___x_5448_;
                } else {
                    v___x_5449_ = lean_array_fget_borrowed(v_as_5440_, v_j_5442_);
                    v___x_5450_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0;
                    v___x_5451_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5452_ = lean_nat_add(v_j_5442_, v___x_5451_);
                    crate::leanh::lean_dec(v_j_5442_);
                    crate::leanh::lean_inc(v___x_5452_);
                    v___x_5453_ = l_Nat_reprFast(v___x_5452_);
                    v___x_5454_ = lean_string_append(v___x_5450_, v___x_5453_);
                    crate::leanh::lean_dec_ref(v___x_5453_);
                    v___x_5455_ = crate::leanh::lean_box(0);
                    v___x_5456_ = l_Lean_Name_str___override(v___x_5455_, v___x_5454_);
                    crate::leanh::lean_inc(v___x_5449_);
                    v___x_5457_ =
                        l_Lean_MVarId_setTag___redArg(v___x_5449_, v___x_5456_, v___y_5444_);
                    if crate::leanh::lean_obj_tag(v___x_5457_) == 0 {
                        v_a_5458_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                        crate::leanh::lean_inc(v_a_5458_);
                        crate::leanh::lean_dec_ref_known(v___x_5457_, 1);
                        v_n_5459_ = lean_nat_sub(v_i_5441_, v___x_5451_);
                        crate::leanh::lean_dec(v_i_5441_);
                        v___x_5460_ = lean_array_push(v_bs_5443_, v_a_5458_);
                        v_i_5441_ = v_n_5459_;
                        v_j_5442_ = v___x_5452_;
                        v_bs_5443_ = v___x_5460_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5452_);
                        crate::leanh::lean_dec_ref(v_bs_5443_);
                        crate::leanh::lean_dec(v_i_5441_);
                        v_a_5462_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                        v_isSharedCheck_5469_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5457_)) as u8;
                        if v_isSharedCheck_5469_ == 0 {
                            v___x_5464_ = v___x_5457_;
                            v_isShared_5465_ = v_isSharedCheck_5469_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5462_);
                            crate::leanh::lean_dec(v___x_5457_);
                            v___x_5464_ = crate::leanh::lean_box(0);
                            v_isShared_5465_ = v_isSharedCheck_5469_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5465_ == 0 {
                    v___x_5467_ = v___x_5464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
                    v___x_5467_ = v_reuseFailAlloc_5468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___boxed(
    mut v_as_5470_: *mut crate::leanh::LeanObject,
    mut v_i_5471_: *mut crate::leanh::LeanObject,
    mut v_j_5472_: *mut crate::leanh::LeanObject,
    mut v_bs_5473_: *mut crate::leanh::LeanObject,
    mut v___y_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5476_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(
            v_as_5470_,
            v_i_5471_,
            v_j_5472_,
            v_bs_5473_,
            v___y_5474_,
        );
    crate::leanh::lean_dec(v___y_5474_);
    crate::leanh::lean_dec_ref(v_as_5470_);
    return v_res_5476_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(
    mut v_mvarId_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5480_ = lean_st_ref_get(v___y_5478_);
    v_mctx_5481_ = crate::leanh::lean_ctor_get(v___x_5480_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5481_);
    crate::leanh::lean_dec(v___x_5480_);
    v_eAssignment_5482_ = crate::leanh::lean_ctor_get(v_mctx_5481_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_5482_);
    crate::leanh::lean_dec_ref(v_mctx_5481_);
    v___x_5483_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_5482_, v_mvarId_5477_);
    crate::leanh::lean_dec_ref(v_eAssignment_5482_);
    v___x_5484_ = crate::leanh::lean_box((v___x_5483_) as usize);
    v___x_5485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5485_, 0, v___x_5484_);
    return v___x_5485_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(
    mut v_mvarId_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5489_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(
            v_mvarId_5486_,
            v___y_5487_,
        );
    crate::leanh::lean_dec(v___y_5487_);
    crate::leanh::lean_dec(v_mvarId_5486_);
    return v_res_5489_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(
    mut v_as_5490_: *mut crate::leanh::LeanObject,
    mut v_i_5491_: usize,
    mut v_stop_5492_: usize,
    mut v_b_5493_: *mut crate::leanh::LeanObject,
    mut v___y_5494_: *mut crate::leanh::LeanObject,
    mut v___y_5495_: *mut crate::leanh::LeanObject,
    mut v___y_5496_: *mut crate::leanh::LeanObject,
    mut v___y_5497_: *mut crate::leanh::LeanObject,
    mut v___y_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: usize = 0;
    let mut v___x_5507_: usize = 0;
    let mut v___x_5509_: u8 = 0;
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: u8 = 0;
    let mut v_a_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: u8 = 0;
    let mut v_a_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5509_ = lean_usize_dec_eq(v_i_5491_, v_stop_5492_);
                if v___x_5509_ == 0 {
                    v___x_5510_ = lean_array_uget_borrowed(v_as_5490_, v_i_5491_);
                    v_mvarId_5513_ = crate::leanh::lean_ctor_get(v___x_5510_, 1);
                    v___x_5514_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_5513_, v___y_5500_);
                    if crate::leanh::lean_obj_tag(v___x_5514_) == 0 {
                        v_a_5515_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                        crate::leanh::lean_inc(v_a_5515_);
                        crate::leanh::lean_dec_ref_known(v___x_5514_, 1);
                        v___x_5516_ = (crate::leanh::lean_unbox(v_a_5515_) as u8);
                        crate::leanh::lean_dec(v_a_5515_);
                        if v___x_5516_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_5505_ = v_b_5493_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_5514_) == 0 {
                            v_a_5517_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                            crate::leanh::lean_inc(v_a_5517_);
                            crate::leanh::lean_dec_ref_known(v___x_5514_, 1);
                            v___x_5518_ = (crate::leanh::lean_unbox(v_a_5517_) as u8);
                            crate::leanh::lean_dec(v_a_5517_);
                            if v___x_5518_ == 0 {
                                v_a_5505_ = v_b_5493_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_5493_);
                            v_a_5519_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                            v_isSharedCheck_5526_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5514_)) as u8;
                            if v_isSharedCheck_5526_ == 0 {
                                v___x_5521_ = v___x_5514_;
                                v_isShared_5522_ = v_isSharedCheck_5526_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5519_);
                                crate::leanh::lean_dec(v___x_5514_);
                                v___x_5521_ = crate::leanh::lean_box(0);
                                v_isShared_5522_ = v_isSharedCheck_5526_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5527_, 0, v_b_5493_);
                    return v___x_5527_;
                }
            }
            1 => {
                v___x_5506_ = 1usize;
                v___x_5507_ = lean_usize_add(v_i_5491_, v___x_5506_);
                v_i_5491_ = v___x_5507_;
                v_b_5493_ = v_a_5505_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v___x_5510_);
                v___x_5512_ = lean_array_push(v_b_5493_, v___x_5510_);
                v_a_5505_ = v___x_5512_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_5522_ == 0 {
                    v___x_5524_ = v___x_5521_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
                    v___x_5524_ = v_reuseFailAlloc_5525_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(
    mut v_as_5528_: *mut crate::leanh::LeanObject,
    mut v_i_5529_: *mut crate::leanh::LeanObject,
    mut v_stop_5530_: *mut crate::leanh::LeanObject,
    mut v_b_5531_: *mut crate::leanh::LeanObject,
    mut v___y_5532_: *mut crate::leanh::LeanObject,
    mut v___y_5533_: *mut crate::leanh::LeanObject,
    mut v___y_5534_: *mut crate::leanh::LeanObject,
    mut v___y_5535_: *mut crate::leanh::LeanObject,
    mut v___y_5536_: *mut crate::leanh::LeanObject,
    mut v___y_5537_: *mut crate::leanh::LeanObject,
    mut v___y_5538_: *mut crate::leanh::LeanObject,
    mut v___y_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5542_: usize = 0;
    let mut v_stop_boxed_5543_: usize = 0;
    let mut v_res_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5542_ = crate::leanh::lean_unbox_usize(v_i_5529_);
    crate::leanh::lean_dec(v_i_5529_);
    v_stop_boxed_5543_ = crate::leanh::lean_unbox_usize(v_stop_5530_);
    crate::leanh::lean_dec(v_stop_5530_);
    v_res_5544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_as_5528_, v_i_boxed_5542_, v_stop_boxed_5543_, v_b_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
    crate::leanh::lean_dec(v___y_5540_);
    crate::leanh::lean_dec_ref(v___y_5539_);
    crate::leanh::lean_dec(v___y_5538_);
    crate::leanh::lean_dec_ref(v___y_5537_);
    crate::leanh::lean_dec(v___y_5536_);
    crate::leanh::lean_dec_ref(v___y_5535_);
    crate::leanh::lean_dec(v___y_5534_);
    crate::leanh::lean_dec_ref(v___y_5533_);
    crate::leanh::lean_dec(v___y_5532_);
    crate::leanh::lean_dec_ref(v_as_5528_);
    return v_res_5544_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5545_ = crate::leanh::lean_box(0);
    v___x_5546_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5547_ = lean_mk_array(v___x_5546_, v___x_5545_);
    return v___x_5547_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5548_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0,
    );
    v___x_5549_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5550_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5550_, 0, v___x_5549_);
    crate::leanh::lean_ctor_set(v___x_5550_, 1, v___x_5548_);
    return v___x_5550_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5551_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5551_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5552_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2,
    );
    v___x_5553_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5553_, 0, v___x_5552_);
    return v___x_5553_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5554_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3,
    );
    v___x_5555_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5556_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5556_, 0, v___x_5555_);
    crate::leanh::lean_ctor_set(v___x_5556_, 1, v___x_5554_);
    crate::leanh::lean_ctor_set(v___x_5556_, 2, v___x_5554_);
    crate::leanh::lean_ctor_set(v___x_5556_, 3, v___x_5554_);
    return v___x_5556_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_run(
    mut v_goal_5557_: *mut crate::leanh::LeanObject,
    mut v_ctx_5558_: *mut crate::leanh::LeanObject,
    mut v_scope_5559_: *mut crate::leanh::LeanObject,
    mut v_stepLimit_x3f_5560_: *mut crate::leanh::LeanObject,
    mut v_a_5561_: *mut crate::leanh::LeanObject,
    mut v_a_5562_: *mut crate::leanh::LeanObject,
    mut v_a_5563_: *mut crate::leanh::LeanObject,
    mut v_a_5564_: *mut crate::leanh::LeanObject,
    mut v_a_5565_: *mut crate::leanh::LeanObject,
    mut v_a_5566_: *mut crate::leanh::LeanObject,
    mut v_a_5567_: *mut crate::leanh::LeanObject,
    mut v_a_5568_: *mut crate::leanh::LeanObject,
    mut v_a_5569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5574_: u8 = 0;
    let mut v_a_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5581_: u8 = 0;
    let mut v___y_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5587_: u8 = 0;
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5591_: u8 = 0;
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: u8 = 0;
    let mut v_initState_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_5606_: u8 = 0;
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: u8 = 0;
    let mut v___x_5614_: u8 = 0;
    let mut v___x_5615_: usize = 0;
    let mut v___x_5616_: usize = 0;
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: usize = 0;
    let mut v___x_5619_: usize = 0;
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5628_: u8 = 0;
    let mut v_a_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5636_: u8 = 0;
    let mut v_a_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5640_: u8 = 0;
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5644_: u8 = 0;
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5649_: u8 = 0;
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5592_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5593_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1,
                );
                v___x_5594_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0;
                v___x_5595_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4,
                );
                if crate::leanh::lean_obj_tag(v_stepLimit_x3f_5560_) == 0 {
                    v___x_5645_ = crate::leanh::lean_box(1);
                    v___y_5597_ = v___x_5645_;
                    state = 5;
                    continue;
                } else {
                    v_val_5646_ = crate::leanh::lean_ctor_get(v_stepLimit_x3f_5560_, 0);
                    v_isSharedCheck_5653_ =
                        (!crate::leanh::lean_is_exclusive(v_stepLimit_x3f_5560_)) as u8;
                    if v_isSharedCheck_5653_ == 0 {
                        v___x_5648_ = v_stepLimit_x3f_5560_;
                        v_isShared_5649_ = v_isSharedCheck_5653_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5646_);
                        crate::leanh::lean_dec(v_stepLimit_x3f_5560_);
                        v___x_5648_ = crate::leanh::lean_box(0);
                        v_isShared_5649_ = v_isSharedCheck_5653_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5576_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5576_, 0, v___y_5572_);
                crate::leanh::lean_ctor_set(v___x_5576_, 1, v_a_5575_);
                crate::leanh::lean_ctor_set(v___x_5576_, 2, v___y_5573_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5576_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_5574_,
                );
                v___x_5577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5577_, 0, v___x_5576_);
                return v___x_5577_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_5582_) == 0 {
                    v_a_5583_ = crate::leanh::lean_ctor_get(v___y_5582_, 0);
                    crate::leanh::lean_inc(v_a_5583_);
                    crate::leanh::lean_dec_ref_known(v___y_5582_, 1);
                    v___y_5572_ = v___y_5579_;
                    v___y_5573_ = v___y_5580_;
                    v___y_5574_ = v___y_5581_;
                    v_a_5575_ = v_a_5583_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_5580_);
                    crate::leanh::lean_dec_ref(v___y_5579_);
                    v_a_5584_ = crate::leanh::lean_ctor_get(v___y_5582_, 0);
                    v_isSharedCheck_5591_ = (!crate::leanh::lean_is_exclusive(v___y_5582_)) as u8;
                    if v_isSharedCheck_5591_ == 0 {
                        v___x_5586_ = v___y_5582_;
                        v_isShared_5587_ = v_isSharedCheck_5591_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5584_);
                        crate::leanh::lean_dec(v___y_5582_);
                        v___x_5586_ = crate::leanh::lean_box(0);
                        v_isShared_5587_ = v_isSharedCheck_5591_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5587_ == 0 {
                    v___x_5589_ = v___x_5586_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
                    v___x_5589_ = v_reuseFailAlloc_5590_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5589_;
            }
            5 => {
                v___x_5598_ = 0;
                v_initState_5599_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                crate::leanh::lean_ctor_set(v_initState_5599_, 0, v___x_5593_);
                crate::leanh::lean_ctor_set(v_initState_5599_, 1, v___x_5593_);
                crate::leanh::lean_ctor_set(v_initState_5599_, 2, v___x_5594_);
                crate::leanh::lean_ctor_set(v_initState_5599_, 3, v___x_5594_);
                crate::leanh::lean_ctor_set(v_initState_5599_, 4, v___x_5595_);
                crate::leanh::lean_ctor_set(v_initState_5599_, 5, v___y_5597_);
                crate::leanh::lean_ctor_set(v_initState_5599_, 6, v___x_5593_);
                crate::leanh::lean_ctor_set_uint8(
                    v_initState_5599_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_5598_,
                );
                v___x_5600_ = lean_st_mk_ref(v_initState_5599_);
                v___x_5601_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(
                    v_scope_5559_,
                    v_goal_5557_,
                    v_ctx_5558_,
                    v___x_5600_,
                    v_a_5561_,
                    v_a_5562_,
                    v_a_5563_,
                    v_a_5564_,
                    v_a_5565_,
                    v_a_5566_,
                    v_a_5567_,
                    v_a_5568_,
                    v_a_5569_,
                );
                if crate::leanh::lean_obj_tag(v___x_5601_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5601_, 1);
                    v___x_5602_ = lean_st_ref_get(v___x_5600_);
                    crate::leanh::lean_dec(v___x_5600_);
                    v_invariants_5603_ = crate::leanh::lean_ctor_get(v___x_5602_, 2);
                    crate::leanh::lean_inc_ref(v_invariants_5603_);
                    v_vcs_5604_ = crate::leanh::lean_ctor_get(v___x_5602_, 3);
                    crate::leanh::lean_inc_ref(v_vcs_5604_);
                    v_inlineHandledInvariants_5605_ = crate::leanh::lean_ctor_get(v___x_5602_, 6);
                    crate::leanh::lean_inc_ref(v_inlineHandledInvariants_5605_);
                    v_preTacFailed_5606_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5602_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    );
                    crate::leanh::lean_dec(v___x_5602_);
                    v___x_5607_ = lean_array_get_size(v_invariants_5603_);
                    v___x_5608_ = lean_mk_empty_array_with_capacity(v___x_5607_);
                    v___x_5609_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_invariants_5603_, v___x_5607_, v___x_5592_, v___x_5608_, v_a_5567_);
                    if crate::leanh::lean_obj_tag(v___x_5609_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5609_, 1);
                        v___x_5610_ = lean_array_get_size(v_vcs_5604_);
                        v___x_5611_ = lean_mk_empty_array_with_capacity(v___x_5610_);
                        v___x_5612_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_vcs_5604_, v___x_5610_, v___x_5592_, v___x_5611_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
                        if crate::leanh::lean_obj_tag(v___x_5612_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5612_, 1);
                            v___x_5613_ = lean_nat_dec_lt(v___x_5592_, v___x_5610_);
                            if v___x_5613_ == 0 {
                                crate::leanh::lean_dec_ref(v_vcs_5604_);
                                v___y_5572_ = v_invariants_5603_;
                                v___y_5573_ = v_inlineHandledInvariants_5605_;
                                v___y_5574_ = v_preTacFailed_5606_;
                                v_a_5575_ = v___x_5594_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5614_ = lean_nat_dec_le(v___x_5610_, v___x_5610_);
                                if v___x_5614_ == 0 {
                                    if v___x_5613_ == 0 {
                                        crate::leanh::lean_dec_ref(v_vcs_5604_);
                                        v___y_5572_ = v_invariants_5603_;
                                        v___y_5573_ = v_inlineHandledInvariants_5605_;
                                        v___y_5574_ = v_preTacFailed_5606_;
                                        v_a_5575_ = v___x_5594_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_5615_ = 0usize;
                                        v___x_5616_ = lean_usize_of_nat(v___x_5610_);
                                        v___x_5617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_vcs_5604_, v___x_5615_, v___x_5616_, v___x_5594_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
                                        crate::leanh::lean_dec_ref(v_vcs_5604_);
                                        v___y_5579_ = v_invariants_5603_;
                                        v___y_5580_ = v_inlineHandledInvariants_5605_;
                                        v___y_5581_ = v_preTacFailed_5606_;
                                        v___y_5582_ = v___x_5617_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___x_5618_ = 0usize;
                                    v___x_5619_ = lean_usize_of_nat(v___x_5610_);
                                    v___x_5620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_vcs_5604_, v___x_5618_, v___x_5619_, v___x_5594_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
                                    crate::leanh::lean_dec_ref(v_vcs_5604_);
                                    v___y_5579_ = v_invariants_5603_;
                                    v___y_5580_ = v_inlineHandledInvariants_5605_;
                                    v___y_5581_ = v_preTacFailed_5606_;
                                    v___y_5582_ = v___x_5620_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_inlineHandledInvariants_5605_);
                            crate::leanh::lean_dec_ref(v_vcs_5604_);
                            crate::leanh::lean_dec_ref(v_invariants_5603_);
                            v_a_5621_ = crate::leanh::lean_ctor_get(v___x_5612_, 0);
                            v_isSharedCheck_5628_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5612_)) as u8;
                            if v_isSharedCheck_5628_ == 0 {
                                v___x_5623_ = v___x_5612_;
                                v_isShared_5624_ = v_isSharedCheck_5628_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5621_);
                                crate::leanh::lean_dec(v___x_5612_);
                                v___x_5623_ = crate::leanh::lean_box(0);
                                v_isShared_5624_ = v_isSharedCheck_5628_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inlineHandledInvariants_5605_);
                        crate::leanh::lean_dec_ref(v_vcs_5604_);
                        crate::leanh::lean_dec_ref(v_invariants_5603_);
                        v_a_5629_ = crate::leanh::lean_ctor_get(v___x_5609_, 0);
                        v_isSharedCheck_5636_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5609_)) as u8;
                        if v_isSharedCheck_5636_ == 0 {
                            v___x_5631_ = v___x_5609_;
                            v_isShared_5632_ = v_isSharedCheck_5636_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5629_);
                            crate::leanh::lean_dec(v___x_5609_);
                            v___x_5631_ = crate::leanh::lean_box(0);
                            v_isShared_5632_ = v_isSharedCheck_5636_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5600_);
                    v_a_5637_ = crate::leanh::lean_ctor_get(v___x_5601_, 0);
                    v_isSharedCheck_5644_ = (!crate::leanh::lean_is_exclusive(v___x_5601_)) as u8;
                    if v_isSharedCheck_5644_ == 0 {
                        v___x_5639_ = v___x_5601_;
                        v_isShared_5640_ = v_isSharedCheck_5644_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5637_);
                        crate::leanh::lean_dec(v___x_5601_);
                        v___x_5639_ = crate::leanh::lean_box(0);
                        v_isShared_5640_ = v_isSharedCheck_5644_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5624_ == 0 {
                    v___x_5626_ = v___x_5623_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
                    v___x_5626_ = v_reuseFailAlloc_5627_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5626_;
            }
            8 => {
                if v_isShared_5632_ == 0 {
                    v___x_5634_ = v___x_5631_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
                    v___x_5634_ = v_reuseFailAlloc_5635_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5634_;
            }
            10 => {
                if v_isShared_5640_ == 0 {
                    v___x_5642_ = v___x_5639_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
                    v___x_5642_ = v_reuseFailAlloc_5643_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5642_;
            }
            12 => {
                if v_isShared_5649_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5648_, 0);
                    v___x_5651_ = v___x_5648_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_val_5646_);
                    v___x_5651_ = v_reuseFailAlloc_5652_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_5597_ = v___x_5651_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(
    mut v_goal_5654_: *mut crate::leanh::LeanObject,
    mut v_ctx_5655_: *mut crate::leanh::LeanObject,
    mut v_scope_5656_: *mut crate::leanh::LeanObject,
    mut v_stepLimit_x3f_5657_: *mut crate::leanh::LeanObject,
    mut v_a_5658_: *mut crate::leanh::LeanObject,
    mut v_a_5659_: *mut crate::leanh::LeanObject,
    mut v_a_5660_: *mut crate::leanh::LeanObject,
    mut v_a_5661_: *mut crate::leanh::LeanObject,
    mut v_a_5662_: *mut crate::leanh::LeanObject,
    mut v_a_5663_: *mut crate::leanh::LeanObject,
    mut v_a_5664_: *mut crate::leanh::LeanObject,
    mut v_a_5665_: *mut crate::leanh::LeanObject,
    mut v_a_5666_: *mut crate::leanh::LeanObject,
    mut v_a_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5668_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(
        v_goal_5654_,
        v_ctx_5655_,
        v_scope_5656_,
        v_stepLimit_x3f_5657_,
        v_a_5658_,
        v_a_5659_,
        v_a_5660_,
        v_a_5661_,
        v_a_5662_,
        v_a_5663_,
        v_a_5664_,
        v_a_5665_,
        v_a_5666_,
    );
    crate::leanh::lean_dec(v_a_5666_);
    crate::leanh::lean_dec_ref(v_a_5665_);
    crate::leanh::lean_dec(v_a_5664_);
    crate::leanh::lean_dec_ref(v_a_5663_);
    crate::leanh::lean_dec(v_a_5662_);
    crate::leanh::lean_dec_ref(v_a_5661_);
    crate::leanh::lean_dec(v_a_5660_);
    crate::leanh::lean_dec_ref(v_a_5659_);
    crate::leanh::lean_dec(v_a_5658_);
    crate::leanh::lean_dec_ref(v_ctx_5655_);
    return v_res_5668_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(
    mut v_mvarId_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
    mut v___y_5675_: *mut crate::leanh::LeanObject,
    mut v___y_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5680_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(
            v_mvarId_5669_,
            v___y_5676_,
        );
    return v___x_5680_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(
    mut v_mvarId_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5692_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(
        v_mvarId_5681_,
        v___y_5682_,
        v___y_5683_,
        v___y_5684_,
        v___y_5685_,
        v___y_5686_,
        v___y_5687_,
        v___y_5688_,
        v___y_5689_,
        v___y_5690_,
    );
    crate::leanh::lean_dec(v___y_5690_);
    crate::leanh::lean_dec_ref(v___y_5689_);
    crate::leanh::lean_dec(v___y_5688_);
    crate::leanh::lean_dec_ref(v___y_5687_);
    crate::leanh::lean_dec(v___y_5686_);
    crate::leanh::lean_dec_ref(v___y_5685_);
    crate::leanh::lean_dec(v___y_5684_);
    crate::leanh::lean_dec_ref(v___y_5683_);
    crate::leanh::lean_dec(v___y_5682_);
    crate::leanh::lean_dec(v_mvarId_5681_);
    return v_res_5692_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(
    mut v_as_5693_: *mut crate::leanh::LeanObject,
    mut v_i_5694_: *mut crate::leanh::LeanObject,
    mut v_j_5695_: *mut crate::leanh::LeanObject,
    mut v_inv_5696_: *mut crate::leanh::LeanObject,
    mut v_bs_5697_: *mut crate::leanh::LeanObject,
    mut v___y_5698_: *mut crate::leanh::LeanObject,
    mut v___y_5699_: *mut crate::leanh::LeanObject,
    mut v___y_5700_: *mut crate::leanh::LeanObject,
    mut v___y_5701_: *mut crate::leanh::LeanObject,
    mut v___y_5702_: *mut crate::leanh::LeanObject,
    mut v___y_5703_: *mut crate::leanh::LeanObject,
    mut v___y_5704_: *mut crate::leanh::LeanObject,
    mut v___y_5705_: *mut crate::leanh::LeanObject,
    mut v___y_5706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5708_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(
            v_as_5693_,
            v_i_5694_,
            v_j_5695_,
            v_bs_5697_,
            v___y_5704_,
        );
    return v___x_5708_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(
    mut v_as_5709_: *mut crate::leanh::LeanObject,
    mut v_i_5710_: *mut crate::leanh::LeanObject,
    mut v_j_5711_: *mut crate::leanh::LeanObject,
    mut v_inv_5712_: *mut crate::leanh::LeanObject,
    mut v_bs_5713_: *mut crate::leanh::LeanObject,
    mut v___y_5714_: *mut crate::leanh::LeanObject,
    mut v___y_5715_: *mut crate::leanh::LeanObject,
    mut v___y_5716_: *mut crate::leanh::LeanObject,
    mut v___y_5717_: *mut crate::leanh::LeanObject,
    mut v___y_5718_: *mut crate::leanh::LeanObject,
    mut v___y_5719_: *mut crate::leanh::LeanObject,
    mut v___y_5720_: *mut crate::leanh::LeanObject,
    mut v___y_5721_: *mut crate::leanh::LeanObject,
    mut v___y_5722_: *mut crate::leanh::LeanObject,
    mut v___y_5723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5724_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(
        v_as_5709_,
        v_i_5710_,
        v_j_5711_,
        v_inv_5712_,
        v_bs_5713_,
        v___y_5714_,
        v___y_5715_,
        v___y_5716_,
        v___y_5717_,
        v___y_5718_,
        v___y_5719_,
        v___y_5720_,
        v___y_5721_,
        v___y_5722_,
    );
    crate::leanh::lean_dec(v___y_5722_);
    crate::leanh::lean_dec_ref(v___y_5721_);
    crate::leanh::lean_dec(v___y_5720_);
    crate::leanh::lean_dec_ref(v___y_5719_);
    crate::leanh::lean_dec(v___y_5718_);
    crate::leanh::lean_dec_ref(v___y_5717_);
    crate::leanh::lean_dec(v___y_5716_);
    crate::leanh::lean_dec_ref(v___y_5715_);
    crate::leanh::lean_dec(v___y_5714_);
    crate::leanh::lean_dec_ref(v_as_5709_);
    return v_res_5724_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(
    mut v_as_5725_: *mut crate::leanh::LeanObject,
    mut v_i_5726_: *mut crate::leanh::LeanObject,
    mut v_j_5727_: *mut crate::leanh::LeanObject,
    mut v_inv_5728_: *mut crate::leanh::LeanObject,
    mut v_bs_5729_: *mut crate::leanh::LeanObject,
    mut v___y_5730_: *mut crate::leanh::LeanObject,
    mut v___y_5731_: *mut crate::leanh::LeanObject,
    mut v___y_5732_: *mut crate::leanh::LeanObject,
    mut v___y_5733_: *mut crate::leanh::LeanObject,
    mut v___y_5734_: *mut crate::leanh::LeanObject,
    mut v___y_5735_: *mut crate::leanh::LeanObject,
    mut v___y_5736_: *mut crate::leanh::LeanObject,
    mut v___y_5737_: *mut crate::leanh::LeanObject,
    mut v___y_5738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5740_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(
            v_as_5725_,
            v_i_5726_,
            v_j_5727_,
            v_bs_5729_,
            v___y_5735_,
            v___y_5736_,
            v___y_5737_,
            v___y_5738_,
        );
    return v___x_5740_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(
    mut v_as_5741_: *mut crate::leanh::LeanObject,
    mut v_i_5742_: *mut crate::leanh::LeanObject,
    mut v_j_5743_: *mut crate::leanh::LeanObject,
    mut v_inv_5744_: *mut crate::leanh::LeanObject,
    mut v_bs_5745_: *mut crate::leanh::LeanObject,
    mut v___y_5746_: *mut crate::leanh::LeanObject,
    mut v___y_5747_: *mut crate::leanh::LeanObject,
    mut v___y_5748_: *mut crate::leanh::LeanObject,
    mut v___y_5749_: *mut crate::leanh::LeanObject,
    mut v___y_5750_: *mut crate::leanh::LeanObject,
    mut v___y_5751_: *mut crate::leanh::LeanObject,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5756_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(
        v_as_5741_,
        v_i_5742_,
        v_j_5743_,
        v_inv_5744_,
        v_bs_5745_,
        v___y_5746_,
        v___y_5747_,
        v___y_5748_,
        v___y_5749_,
        v___y_5750_,
        v___y_5751_,
        v___y_5752_,
        v___y_5753_,
        v___y_5754_,
    );
    crate::leanh::lean_dec(v___y_5754_);
    crate::leanh::lean_dec_ref(v___y_5753_);
    crate::leanh::lean_dec(v___y_5752_);
    crate::leanh::lean_dec_ref(v___y_5751_);
    crate::leanh::lean_dec(v___y_5750_);
    crate::leanh::lean_dec_ref(v___y_5749_);
    crate::leanh::lean_dec(v___y_5748_);
    crate::leanh::lean_dec_ref(v___y_5747_);
    crate::leanh::lean_dec(v___y_5746_);
    crate::leanh::lean_dec_ref(v_as_5741_);
    return v_res_5756_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
}
