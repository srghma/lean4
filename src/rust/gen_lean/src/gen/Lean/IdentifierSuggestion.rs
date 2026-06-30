// Lean compiler output
// Module: Lean.IdentifierSuggestion
// Imports: Lean.Elab.DeclModifiers Lean.Elab.ErrorUtils Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Name_eraseSuffix_x3f, l_Lean_Name_replacePrefix, l_Lean_Syntax_instRepr_repr,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getId, l_Lean_replaceRef, l_List_lengthTR___redArg, l_id___boxed,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
    l_Lean_Name_quickLt,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::DeclModifiers::{
    initialize_Lean_Elab_DeclModifiers, runtime_initialize_Lean_Elab_DeclModifiers,
};
use crate::r#gen::Lean::Elab::ErrorUtils::{
    initialize_Lean_Elab_ErrorUtils, runtime_initialize_Lean_Elab_ErrorUtils,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedPersistentEnvExtensionState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_fvarId_x21, l_Lean_Expr_isFVar};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hint_x27, l_Lean_MessageData_joinSep, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_FVarId_getUserName___redArg;
use crate::r#gen::Lean::Meta::Hint::l_Lean_MessageData_hint;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ResolveName::l_Lean_ResolveName_resolveGlobalName;
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 83, 117, 103, 103, 101, 115, 116, 70,
        111, 114, 65, 116, 116, 114, 0,
    ],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6_value:
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
        101, 120, 105, 115, 116, 105, 110, 103, 84, 111, 73, 110, 99, 111, 114, 114, 101, 99, 116,
        0,
    ],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6_value
) as *mut leanh::LeanObject;
static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value) as *mut leanh::LeanObject,2708381791570870936 as *mut leanh::LeanObject] };
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__6_value) as *mut leanh::LeanObject,16745285037689313413 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10_value: leanh::LeanCtorObject<8> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1_value:
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
        105, 110, 99, 111, 114, 114, 101, 99, 116, 84, 111, 69, 120, 105, 115, 116, 105, 110, 103,
        0,
    ],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1_value
) as *mut leanh::LeanObject;
static l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__5_value) as *mut leanh::LeanObject,2708381791570870936 as *mut leanh::LeanObject] };
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__1_value) as *mut leanh::LeanObject,11411336900885264973 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value:
    leanh::LeanCtorObject<8> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 8
            + 0) as u16,
        other: 8,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__8_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__9_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__1_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__2_value
        ) as *mut leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__3_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<42> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [67, 97, 110, 110, 111, 116, 32, 109, 97, 107, 101, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 112, 114, 105, 118, 97, 116, 101, 32, 110, 97, 109, 101, 115, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<42> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 115, 117, 103, 103, 101, 115, 116, 95, 102, 111, 114, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 32, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [73, 100, 101, 110, 116, 105, 102, 105, 101, 114, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16557539032595930038 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,15906169506248608095 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4_value) as *mut leanh::LeanObject,13191449396672823826 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 73, 109, 112, 108, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15240786484577382703 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 117, 103, 103, 101, 115, 116, 95, 102, 111, 114, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8372811248341252874 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanStringObject<115> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 115, m_capacity: 115, m_length: 114, m_data: [115, 117, 103, 103, 101, 115, 116, 32, 111, 116, 104, 101, 114, 32, 40, 105, 110, 99, 111, 114, 114, 101, 99, 116, 44, 32, 110, 111, 116, 45, 101, 120, 105, 115, 116, 105, 110, 103, 41, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 116, 104, 97, 116, 32, 115, 111, 109, 101, 111, 110, 101, 32, 109, 105, 103, 104, 116, 32, 117, 115, 101, 32, 119, 104, 101, 110, 32, 116, 104, 101, 121, 32, 97, 99, 116, 117, 97, 108, 108, 121, 32, 119, 97, 110, 116, 32, 116, 104, 105, 115, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__12_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getSuggestions___redArg___lam__1___closed__0_value:
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
static mut l_Lean_getSuggestions___redArg___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__7_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__8_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__9_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__10_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___lam__1___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_getSuggestions___redArg___lam__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___lam__1___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_getSuggestions___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getSuggestions___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_NameSet_insert as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getSuggestions___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getSuggestions___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getSuggestions___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getSuggestions___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 104, 97, 110, 103, 101, 32, 116, 111, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [85, 110, 107, 110, 111, 119, 110, 32, 0],
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 96, 0],
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        80, 101, 114, 104, 97, 112, 115, 32, 121, 111, 117, 32, 109, 101, 97, 110, 116, 32, 0,
    ],
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        32, 105, 110, 32, 112, 108, 97, 99, 101, 32, 111, 102, 32, 96, 0,
    ],
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 115, 101, 0],
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [226, 128, 162, 32, 96, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0_value
) as *mut leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        84, 104, 101, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2_value:
    leanh::LeanStringObject<181> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 181,
    m_capacity: 181,
    m_length: 180,
    m_data: [
        96, 32, 105, 115, 32, 117, 110, 107, 110, 111, 119, 110, 44, 32, 97, 110, 100, 32, 76, 101,
        97, 110, 39, 115, 32, 96, 97, 117, 116, 111, 73, 109, 112, 108, 105, 99, 105, 116, 96, 32,
        111, 112, 116, 105, 111, 110, 32, 99, 97, 117, 115, 101, 115, 32, 97, 110, 32, 117, 110,
        107, 110, 111, 119, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 116,
        111, 32, 98, 101, 32, 116, 114, 101, 97, 116, 101, 100, 32, 97, 115, 32, 97, 110, 32, 105,
        109, 112, 108, 105, 99, 105, 116, 108, 121, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114,
        105, 97, 98, 108, 101, 32, 119, 105, 116, 104, 32, 97, 110, 32, 117, 110, 107, 110, 111,
        119, 110, 32, 116, 121, 112, 101, 46, 32, 72, 111, 119, 101, 118, 101, 114, 44, 32, 116,
        104, 101, 32, 117, 110, 107, 110, 111, 119, 110, 32, 116, 121, 112, 101, 32, 99, 97, 110,
        110, 111, 116, 32, 98, 101, 32, 0,
    ],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [44, 32, 97, 110, 100, 32, 0],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6_value:
    leanh::LeanStringObject<106> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 106,
    m_capacity: 106,
    m_length: 105,
    m_data: [
        32, 105, 115, 32, 119, 104, 97, 116, 32, 76, 101, 97, 110, 32, 101, 120, 112, 101, 99, 116,
        115, 32, 104, 101, 114, 101, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 111, 102, 116,
        101, 110, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 32, 111, 102, 32, 97, 32,
        116, 121, 112, 111, 32, 111, 114, 32, 97, 32, 109, 105, 115, 115, 105, 110, 103, 32, 96,
        105, 109, 112, 111, 114, 116, 96, 32, 111, 114, 32, 96, 111, 112, 101, 110, 96, 32, 115,
        116, 97, 116, 101, 109, 101, 110, 116, 46, 0,
    ],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9_value:
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
        80, 101, 114, 104, 97, 112, 115, 32, 121, 111, 117, 32, 109, 101, 97, 110, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        96, 32, 105, 110, 32, 112, 108, 97, 99, 101, 32, 111, 102, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [96, 63, 0],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        80, 101, 114, 104, 97, 112, 115, 32, 121, 111, 117, 32, 109, 101, 97, 110, 116, 32, 111,
        110, 101, 32, 111, 102, 32, 116, 104, 101, 115, 101, 32, 105, 110, 32, 112, 108, 97, 99,
        101, 32, 111, 102, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [96, 58, 0],
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(
    mut v_as_2126_: *mut leanh::LeanObject,
    mut v_i_2127_: usize,
    mut v_stop_2128_: usize,
    mut v_b_2129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: usize = 0;
    let mut v___x_2134_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2130_ = lean_usize_dec_eq(v_i_2127_, v_stop_2128_);
                if v___x_2130_ == 0 {
                    v___x_2131_ = lean_array_uget_borrowed(v_as_2126_, v_i_2127_);
                    leanh::lean_inc(v___x_2131_);
                    v___x_2132_ = l_Lean_NameSet_insert(v_b_2129_, v___x_2131_);
                    v___x_2133_ = 1usize;
                    v___x_2134_ = lean_usize_add(v_i_2127_, v___x_2133_);
                    v_i_2127_ = v___x_2134_;
                    v_b_2129_ = v___x_2132_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2129_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4___boxed(
    mut v_as_2136_: *mut leanh::LeanObject,
    mut v_i_2137_: *mut leanh::LeanObject,
    mut v_stop_2138_: *mut leanh::LeanObject,
    mut v_b_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2140_: usize = 0;
    let mut v_stop_boxed_2141_: usize = 0;
    let mut v_res_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2140_ = leanh::lean_unbox_usize(v_i_2137_);
    leanh::lean_dec(v_i_2137_);
    v_stop_boxed_2141_ = leanh::lean_unbox_usize(v_stop_2138_);
    leanh::lean_dec(v_stop_2138_);
    v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_as_2136_, v_i_boxed_2140_, v_stop_boxed_2141_, v_b_2139_);
    leanh::lean_dec_ref(v_as_2136_);
    return v_res_2142_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(
    mut v_snd_2143_: *mut leanh::LeanObject,
    mut v_old_2144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: u8 = 0;
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: usize = 0;
    let mut v___x_2154_: usize = 0;
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: usize = 0;
    let mut v___x_2158_: usize = 0;
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_old_2144_) == 0 {
                    v___x_2161_ = l_Lean_NameSet_empty;
                    v___y_2146_ = v___x_2161_;
                    state = 1;
                    continue;
                } else {
                    v_val_2162_ = leanh::lean_ctor_get(v_old_2144_, 0);
                    leanh::lean_inc(v_val_2162_);
                    leanh::lean_dec_ref_known(v_old_2144_, 1);
                    v___y_2146_ = v_val_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2147_ = leanh::lean_unsigned_to_nat(0);
                v___x_2148_ = lean_array_get_size(v_snd_2143_);
                v___x_2149_ = lean_nat_dec_lt(v___x_2147_, v___x_2148_);
                if v___x_2149_ == 0 {
                    v___x_2150_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2150_, 0, v___y_2146_);
                    return v___x_2150_;
                } else {
                    v___x_2151_ = lean_nat_dec_le(v___x_2148_, v___x_2148_);
                    if v___x_2151_ == 0 {
                        if v___x_2149_ == 0 {
                            v___x_2152_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2152_, 0, v___y_2146_);
                            return v___x_2152_;
                        } else {
                            v___x_2153_ = 0usize;
                            v___x_2154_ = lean_usize_of_nat(v___x_2148_);
                            v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_2143_, v___x_2153_, v___x_2154_, v___y_2146_);
                            v___x_2156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2156_, 0, v___x_2155_);
                            return v___x_2156_;
                        }
                    } else {
                        v___x_2157_ = 0usize;
                        v___x_2158_ = lean_usize_of_nat(v___x_2148_);
                        v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_2143_, v___x_2157_, v___x_2158_, v___y_2146_);
                        v___x_2160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2160_, 0, v___x_2159_);
                        return v___x_2160_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0___boxed(
    mut v_snd_2163_: *mut leanh::LeanObject,
    mut v_old_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2165_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_2163_, v_old_2164_);
    leanh::lean_dec_ref(v_snd_2163_);
    return v_res_2165_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(
    mut v_snd_2166_: *mut leanh::LeanObject,
    mut v_k_2167_: *mut leanh::LeanObject,
    mut v_t_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v___x_2177_: u8 = 0;
    let mut v_impl_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2168_) == 0 {
                    v_size_2169_ = leanh::lean_ctor_get(v_t_2168_, 0);
                    v_k_2170_ = leanh::lean_ctor_get(v_t_2168_, 1);
                    v_v_2171_ = leanh::lean_ctor_get(v_t_2168_, 2);
                    v_l_2172_ = leanh::lean_ctor_get(v_t_2168_, 3);
                    v_r_2173_ = leanh::lean_ctor_get(v_t_2168_, 4);
                    v_isSharedCheck_2188_ = (!leanh::lean_is_exclusive(v_t_2168_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2175_ = v_t_2168_;
                        v_isShared_2176_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2173_);
                        leanh::lean_inc(v_l_2172_);
                        leanh::lean_inc(v_v_2171_);
                        leanh::lean_inc(v_k_2170_);
                        leanh::lean_inc(v_size_2169_);
                        leanh::lean_dec(v_t_2168_);
                        v___x_2175_ = leanh::lean_box(0);
                        v_isShared_2176_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2189_ = leanh::lean_box(0);
                    v___x_2190_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_2166_, v___x_2189_);
                    v_val_2191_ = leanh::lean_ctor_get(v___x_2190_, 0);
                    leanh::lean_inc(v_val_2191_);
                    leanh::lean_dec(v___x_2190_);
                    v___x_2192_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2193_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_2193_, 0, v___x_2192_);
                    leanh::lean_ctor_set(v___x_2193_, 1, v_k_2167_);
                    leanh::lean_ctor_set(v___x_2193_, 2, v_val_2191_);
                    leanh::lean_ctor_set(v___x_2193_, 3, v_t_2168_);
                    leanh::lean_ctor_set(v___x_2193_, 4, v_t_2168_);
                    return v___x_2193_;
                }
            }
            1 => {
                v___x_2177_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2167_, v_k_2170_);
                match v___x_2177_ {
                    0 => {
                        leanh::lean_del_object(v___x_2175_);
                        leanh::lean_dec(v_size_2169_);
                        v_impl_2178_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_2166_, v_k_2167_, v_l_2172_);
                        v___x_2179_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_2170_,
                            v_v_2171_,
                            v_impl_2178_,
                            v_r_2173_,
                        );
                        return v___x_2179_;
                    }
                    1 => {
                        leanh::lean_dec(v_k_2170_);
                        v___x_2180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2180_, 0, v_v_2171_);
                        v___x_2181_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___lam__0(v_snd_2166_, v___x_2180_);
                        v_val_2182_ = leanh::lean_ctor_get(v___x_2181_, 0);
                        leanh::lean_inc(v_val_2182_);
                        leanh::lean_dec(v___x_2181_);
                        if v_isShared_2176_ == 0 {
                            leanh::lean_ctor_set(v___x_2175_, 2, v_val_2182_);
                            leanh::lean_ctor_set(v___x_2175_, 1, v_k_2167_);
                            v___x_2184_ = v___x_2175_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2185_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_size_2169_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_k_2167_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_val_2182_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_l_2172_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 4, v_r_2173_);
                            v___x_2184_ = v_reuseFailAlloc_2185_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_del_object(v___x_2175_);
                        leanh::lean_dec(v_size_2169_);
                        v_impl_2186_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_2166_, v_k_2167_, v_r_2173_);
                        v___x_2187_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_2170_,
                            v_v_2171_,
                            v_l_2172_,
                            v_impl_2186_,
                        );
                        return v___x_2187_;
                    }
                }
            }
            2 => {
                return v___x_2184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg___boxed(
    mut v_snd_2194_: *mut leanh::LeanObject,
    mut v_k_2195_: *mut leanh::LeanObject,
    mut v_t_2196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2197_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_2194_, v_k_2195_, v_t_2196_);
    leanh::lean_dec_ref(v_snd_2194_);
    return v_res_2197_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__0(
    mut v_table_2198_: *mut leanh::LeanObject,
    mut v_x_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2200_ = leanh::lean_ctor_get(v_x_2199_, 0);
    leanh::lean_inc(v_fst_2200_);
    v_snd_2201_ = leanh::lean_ctor_get(v_x_2199_, 1);
    leanh::lean_inc(v_snd_2201_);
    leanh::lean_dec_ref(v_x_2199_);
    v___x_2202_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_2201_, v_fst_2200_, v_table_2198_);
    leanh::lean_dec(v_snd_2201_);
    return v___x_2202_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(
    mut v_a_2203_: *mut leanh::LeanObject,
    mut v_b_2204_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: u8 = 0;
    v_fst_2205_ = leanh::lean_ctor_get(v_a_2203_, 0);
    v_fst_2206_ = leanh::lean_ctor_get(v_b_2204_, 0);
    v___x_2207_ = l_Lean_Name_quickLt(v_fst_2205_, v_fst_2206_);
    return v___x_2207_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0___boxed(
    mut v_a_2208_: *mut leanh::LeanObject,
    mut v_b_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2210_: u8 = 0;
    let mut v_r_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_2208_, v_b_2209_);
    leanh::lean_dec_ref(v_b_2209_);
    leanh::lean_dec_ref(v_a_2208_);
    v_r_2211_ = leanh::lean_box((v_res_2210_) as usize);
    return v_r_2211_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(
    mut v_hi_2212_: *mut leanh::LeanObject,
    mut v_pivot_2213_: *mut leanh::LeanObject,
    mut v_as_2214_: *mut leanh::LeanObject,
    mut v_i_2215_: *mut leanh::LeanObject,
    mut v_k_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: u8 = 0;
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2217_ = lean_nat_dec_lt(v_k_2216_, v_hi_2212_);
                if v___x_2217_ == 0 {
                    leanh::lean_dec(v_k_2216_);
                    v___x_2218_ = lean_array_fswap(v_as_2214_, v_i_2215_, v_hi_2212_);
                    v___x_2219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2219_, 0, v_i_2215_);
                    leanh::lean_ctor_set(v___x_2219_, 1, v___x_2218_);
                    return v___x_2219_;
                } else {
                    v___x_2220_ = lean_array_fget_borrowed(v_as_2214_, v_k_2216_);
                    v_fst_2221_ = leanh::lean_ctor_get(v___x_2220_, 0);
                    v_fst_2222_ = leanh::lean_ctor_get(v_pivot_2213_, 0);
                    v___x_2223_ = l_Lean_Name_quickLt(v_fst_2221_, v_fst_2222_);
                    if v___x_2223_ == 0 {
                        v___x_2224_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2225_ = lean_nat_add(v_k_2216_, v___x_2224_);
                        leanh::lean_dec(v_k_2216_);
                        v_k_2216_ = v___x_2225_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2227_ = lean_array_fswap(v_as_2214_, v_i_2215_, v_k_2216_);
                        v___x_2228_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2229_ = lean_nat_add(v_i_2215_, v___x_2228_);
                        leanh::lean_dec(v_i_2215_);
                        v___x_2230_ = lean_nat_add(v_k_2216_, v___x_2228_);
                        leanh::lean_dec(v_k_2216_);
                        v_as_2214_ = v___x_2227_;
                        v_i_2215_ = v___x_2229_;
                        v_k_2216_ = v___x_2230_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg___boxed(
    mut v_hi_2232_: *mut leanh::LeanObject,
    mut v_pivot_2233_: *mut leanh::LeanObject,
    mut v_as_2234_: *mut leanh::LeanObject,
    mut v_i_2235_: *mut leanh::LeanObject,
    mut v_k_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_2232_, v_pivot_2233_, v_as_2234_, v_i_2235_, v_k_2236_);
    leanh::lean_dec_ref(v_pivot_2233_);
    leanh::lean_dec(v_hi_2232_);
    return v_res_2237_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(
    mut v_n_2238_: *mut leanh::LeanObject,
    mut v_as_2239_: *mut leanh::LeanObject,
    mut v_lo_2240_: *mut leanh::LeanObject,
    mut v_hi_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2253_ = lean_nat_dec_lt(v_lo_2240_, v_hi_2241_);
                if v___x_2253_ == 0 {
                    leanh::lean_dec(v_lo_2240_);
                    return v_as_2239_;
                } else {
                    v___x_2254_ = lean_nat_add(v_lo_2240_, v_hi_2241_);
                    v___x_2255_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2256_ = lean_nat_shiftr(v___x_2254_, v___x_2255_);
                    leanh::lean_dec(v___x_2254_);
                    v___x_2269_ = lean_array_fget_borrowed(v_as_2239_, v_mid_2256_);
                    v___x_2270_ = lean_array_fget_borrowed(v_as_2239_, v_lo_2240_);
                    v___x_2271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_2269_, v___x_2270_);
                    if v___x_2271_ == 0 {
                        v___y_2264_ = v_as_2239_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2272_ = lean_array_fswap(v_as_2239_, v_lo_2240_, v_mid_2256_);
                        v___y_2264_ = v___x_2272_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2244_ = lean_array_fget(v___y_2243_, v_hi_2241_);
                leanh::lean_inc_n(v_lo_2240_, 2);
                v___x_2245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_2241_, v_pivot_2244_, v___y_2243_, v_lo_2240_, v_lo_2240_);
                leanh::lean_dec(v_pivot_2244_);
                v_fst_2246_ = leanh::lean_ctor_get(v___x_2245_, 0);
                leanh::lean_inc(v_fst_2246_);
                v_snd_2247_ = leanh::lean_ctor_get(v___x_2245_, 1);
                leanh::lean_inc(v_snd_2247_);
                leanh::lean_dec_ref(v___x_2245_);
                v___x_2248_ = lean_nat_dec_le(v_hi_2241_, v_fst_2246_);
                if v___x_2248_ == 0 {
                    v___x_2249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_2238_, v_snd_2247_, v_lo_2240_, v_fst_2246_);
                    v___x_2250_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2251_ = lean_nat_add(v_fst_2246_, v___x_2250_);
                    leanh::lean_dec(v_fst_2246_);
                    v_as_2239_ = v___x_2249_;
                    v_lo_2240_ = v___x_2251_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2246_);
                    leanh::lean_dec(v_lo_2240_);
                    return v_snd_2247_;
                }
            }
            2 => {
                v___x_2259_ = lean_array_fget_borrowed(v___y_2258_, v_mid_2256_);
                v___x_2260_ = lean_array_fget_borrowed(v___y_2258_, v_hi_2241_);
                v___x_2261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_2259_, v___x_2260_);
                if v___x_2261_ == 0 {
                    leanh::lean_dec(v_mid_2256_);
                    v___y_2243_ = v___y_2258_;
                    state = 1;
                    continue;
                } else {
                    v___x_2262_ = lean_array_fswap(v___y_2258_, v_mid_2256_, v_hi_2241_);
                    leanh::lean_dec(v_mid_2256_);
                    v___y_2243_ = v___x_2262_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2265_ = lean_array_fget_borrowed(v___y_2264_, v_hi_2241_);
                v___x_2266_ = lean_array_fget_borrowed(v___y_2264_, v_lo_2240_);
                v___x_2267_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v___x_2265_, v___x_2266_);
                if v___x_2267_ == 0 {
                    v___y_2258_ = v___y_2264_;
                    state = 2;
                    continue;
                } else {
                    v___x_2268_ = lean_array_fswap(v___y_2264_, v_lo_2240_, v_hi_2241_);
                    v___y_2258_ = v___x_2268_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___boxed(
    mut v_n_2273_: *mut leanh::LeanObject,
    mut v_as_2274_: *mut leanh::LeanObject,
    mut v_lo_2275_: *mut leanh::LeanObject,
    mut v_hi_2276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_2273_, v_as_2274_, v_lo_2275_, v_hi_2276_);
    leanh::lean_dec(v_hi_2276_);
    leanh::lean_dec(v_n_2273_);
    return v_res_2277_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(
    mut v_init_2278_: *mut leanh::LeanObject,
    mut v_x_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2279_) == 0 {
                    v_k_2280_ = leanh::lean_ctor_get(v_x_2279_, 1);
                    leanh::lean_inc(v_k_2280_);
                    v_l_2281_ = leanh::lean_ctor_get(v_x_2279_, 3);
                    leanh::lean_inc(v_l_2281_);
                    v_r_2282_ = leanh::lean_ctor_get(v_x_2279_, 4);
                    leanh::lean_inc(v_r_2282_);
                    leanh::lean_dec_ref_known(v_x_2279_, 5);
                    v___x_2283_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_2278_, v_l_2281_);
                    v___x_2284_ = lean_array_push(v___x_2283_, v_k_2280_);
                    v_init_2278_ = v___x_2284_;
                    v_x_2279_ = v_r_2282_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2278_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(
    mut v_sz_2286_: usize,
    mut v_i_2287_: usize,
    mut v_bs_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2289_: u8 = 0;
    let mut v_v_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: usize = 0;
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2289_ = lean_usize_dec_lt(v_i_2287_, v_sz_2286_);
                if v___x_2289_ == 0 {
                    return v_bs_2288_;
                } else {
                    v_v_2290_ = lean_array_uget(v_bs_2288_, v_i_2287_);
                    v_fst_2291_ = leanh::lean_ctor_get(v_v_2290_, 0);
                    v_snd_2292_ = leanh::lean_ctor_get(v_v_2290_, 1);
                    v_isSharedCheck_2310_ = (!leanh::lean_is_exclusive(v_v_2290_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v___x_2294_ = v_v_2290_;
                        v_isShared_2295_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2292_);
                        leanh::lean_inc(v_fst_2291_);
                        leanh::lean_dec(v_v_2290_);
                        v___x_2294_ = leanh::lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2296_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_2297_ = lean_array_uset(v_bs_2288_, v_i_2287_, v___x_2296_);
                if leanh::lean_obj_tag(v_snd_2292_) == 0 {
                    v_size_2309_ = leanh::lean_ctor_get(v_snd_2292_, 0);
                    leanh::lean_inc(v_size_2309_);
                    v___y_2299_ = v_size_2309_;
                    state = 2;
                    continue;
                } else {
                    v___y_2299_ = v___x_2296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2300_ = lean_mk_empty_array_with_capacity(v___y_2299_);
                leanh::lean_dec(v___y_2299_);
                v___x_2301_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_2300_, v_snd_2292_);
                if v_isShared_2295_ == 0 {
                    leanh::lean_ctor_set(v___x_2294_, 1, v___x_2301_);
                    v___x_2303_ = v___x_2294_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_fst_2291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2301_);
                    v___x_2303_ = v_reuseFailAlloc_2308_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2304_ = 1usize;
                v___x_2305_ = lean_usize_add(v_i_2287_, v___x_2304_);
                v___x_2306_ = lean_array_uset(v_bs_x27_2297_, v_i_2287_, v___x_2303_);
                v_i_2287_ = v___x_2305_;
                v_bs_2288_ = v___x_2306_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2___boxed(
    mut v_sz_2311_: *mut leanh::LeanObject,
    mut v_i_2312_: *mut leanh::LeanObject,
    mut v_bs_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2314_: usize = 0;
    let mut v_i_boxed_2315_: usize = 0;
    let mut v_res_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2314_ = leanh::lean_unbox_usize(v_sz_2311_);
    leanh::lean_dec(v_sz_2311_);
    v_i_boxed_2315_ = leanh::lean_unbox_usize(v_i_2312_);
    leanh::lean_dec(v_i_2312_);
    v_res_2316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_boxed_2314_, v_i_boxed_2315_, v_bs_2313_);
    return v_res_2316_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(
    mut v_init_2317_: *mut leanh::LeanObject,
    mut v_x_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2318_) == 0 {
                    v_k_2319_ = leanh::lean_ctor_get(v_x_2318_, 1);
                    v_v_2320_ = leanh::lean_ctor_get(v_x_2318_, 2);
                    v_l_2321_ = leanh::lean_ctor_get(v_x_2318_, 3);
                    v_r_2322_ = leanh::lean_ctor_get(v_x_2318_, 4);
                    v___x_2323_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_2317_, v_l_2321_);
                    leanh::lean_inc(v_v_2320_);
                    leanh::lean_inc(v_k_2319_);
                    v___x_2324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2324_, 0, v_k_2319_);
                    leanh::lean_ctor_set(v___x_2324_, 1, v_v_2320_);
                    v___x_2325_ = lean_array_push(v___x_2323_, v___x_2324_);
                    v_init_2317_ = v___x_2325_;
                    v_x_2318_ = v_r_2322_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2317_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2___boxed(
    mut v_init_2327_: *mut leanh::LeanObject,
    mut v_x_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_2327_, v_x_2328_);
    leanh::lean_dec(v_x_2328_);
    return v_res_2329_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(
    mut v_x_2332_: *mut leanh::LeanObject,
    mut v_s_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: u8 = 0;
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = leanh::lean_unsigned_to_nat(0);
                v___x_2335_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0;
                v___x_2336_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_2335_, v_s_2333_);
                v_sz_2337_ = lean_array_size(v___x_2336_);
                v___x_2338_ = 0usize;
                v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_2337_, v___x_2338_, v___x_2336_);
                v___x_2340_ = lean_array_get_size(v___x_2339_);
                v___x_2346_ = lean_nat_dec_eq(v___x_2340_, v___x_2334_);
                if v___x_2346_ == 0 {
                    v___x_2347_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2348_ = lean_nat_sub(v___x_2340_, v___x_2347_);
                    v___x_2352_ = lean_nat_dec_le(v___x_2334_, v___x_2348_);
                    if v___x_2352_ == 0 {
                        leanh::lean_inc(v___x_2348_);
                        v___y_2350_ = v___x_2348_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2350_ = v___x_2334_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref_n(v___x_2339_, 2);
                    v___x_2353_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2353_, 0, v___x_2339_);
                    leanh::lean_ctor_set(v___x_2353_, 1, v___x_2339_);
                    leanh::lean_ctor_set(v___x_2353_, 2, v___x_2339_);
                    return v___x_2353_;
                }
            }
            1 => {
                v___x_2344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_2340_, v___x_2339_, v___y_2342_, v___y_2343_);
                leanh::lean_dec(v___y_2343_);
                leanh::lean_inc_ref_n(v___x_2344_, 2);
                v___x_2345_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2345_, 0, v___x_2344_);
                leanh::lean_ctor_set(v___x_2345_, 1, v___x_2344_);
                leanh::lean_ctor_set(v___x_2345_, 2, v___x_2344_);
                return v___x_2345_;
            }
            2 => {
                v___x_2351_ = lean_nat_dec_le(v___y_2350_, v___x_2348_);
                if v___x_2351_ == 0 {
                    leanh::lean_dec(v___x_2348_);
                    leanh::lean_inc(v___y_2350_);
                    v___y_2342_ = v___y_2350_;
                    v___y_2343_ = v___y_2350_;
                    state = 1;
                    continue;
                } else {
                    v___y_2342_ = v___y_2350_;
                    v___y_2343_ = v___x_2348_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___boxed(
    mut v_x_2354_: *mut leanh::LeanObject,
    mut v_s_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2356_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1(
        v_x_2354_, v_s_2355_,
    );
    leanh::lean_dec(v_s_2355_);
    leanh::lean_dec_ref(v_x_2354_);
    return v_res_2356_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(
    mut v_x_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = leanh::lean_box(0);
    return v___x_2358_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2___boxed(
    mut v_x_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ =
        l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__2(v_x_2359_);
    leanh::lean_dec(v_x_2359_);
    return v_res_2360_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(
    mut v_table_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2365_: usize = 0;
    let mut v___x_2366_: usize = 0;
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2362_ = leanh::lean_unsigned_to_nat(0);
                v___x_2363_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__1___closed__0;
                v___x_2364_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v___x_2363_, v_table_2361_);
                v_sz_2365_ = lean_array_size(v___x_2364_);
                v___x_2366_ = 0usize;
                v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__2(v_sz_2365_, v___x_2366_, v___x_2364_);
                v___x_2368_ = lean_array_get_size(v___x_2367_);
                v___x_2369_ = lean_nat_dec_eq(v___x_2368_, v___x_2362_);
                if v___x_2369_ == 0 {
                    v___x_2370_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2371_ = lean_nat_sub(v___x_2368_, v___x_2370_);
                    v___x_2377_ = lean_nat_dec_le(v___x_2362_, v___x_2371_);
                    if v___x_2377_ == 0 {
                        leanh::lean_inc(v___x_2371_);
                        v___y_2373_ = v___x_2371_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2373_ = v___x_2362_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2367_;
                }
            }
            1 => {
                v___x_2374_ = lean_nat_dec_le(v___y_2373_, v___x_2371_);
                if v___x_2374_ == 0 {
                    leanh::lean_dec(v___x_2371_);
                    leanh::lean_inc(v___y_2373_);
                    v___x_2375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_2368_, v___x_2367_, v___y_2373_, v___y_2373_);
                    leanh::lean_dec(v___y_2373_);
                    return v___x_2375_;
                } else {
                    v___x_2376_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v___x_2368_, v___x_2367_, v___y_2373_, v___x_2371_);
                    leanh::lean_dec(v___x_2371_);
                    return v___x_2376_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3___boxed(
    mut v_table_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2379_ =
        l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__3(v_table_2378_);
    leanh::lean_dec(v_table_2378_);
    return v_res_2379_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(
    mut v___x_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2382_, 0, v___x_2380_);
    return v___x_2382_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4___boxed(
    mut v___x_2383_: *mut leanh::LeanObject,
    mut v___y_2384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ =
        l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__4(v___x_2383_);
    return v_res_2385_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(
    mut v___x_2386_: *mut leanh::LeanObject,
    mut v_x_2387_: *mut leanh::LeanObject,
    mut v___y_2388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2390_, 0, v___x_2386_);
    return v___x_2390_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5___boxed(
    mut v___x_2391_: *mut leanh::LeanObject,
    mut v_x_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
    mut v___y_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___lam__5(
        v___x_2391_,
        v_x_2392_,
        v___y_2393_,
    );
    leanh::lean_dec_ref(v___y_2393_);
    leanh::lean_dec_ref(v_x_2392_);
    return v_res_2395_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect()
-> *mut leanh::LeanObject {
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__11;
    v___x_2425_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2424_);
    return v___x_2425_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___boxed(
    mut v_a_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2427_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
    return v_res_2427_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0(
    mut v_init_2428_: *mut leanh::LeanObject,
    mut v_t_2429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v_init_2428_, v_t_2429_);
    return v___x_2430_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(
    mut v_init_2431_: *mut leanh::LeanObject,
    mut v_t_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1_spec__2(v_init_2431_, v_t_2432_);
    return v___x_2433_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1___boxed(
    mut v_init_2434_: *mut leanh::LeanObject,
    mut v_t_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__1(v_init_2434_, v_t_2435_);
    leanh::lean_dec(v_t_2435_);
    return v_res_2436_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(
    mut v_n_2437_: *mut leanh::LeanObject,
    mut v_as_2438_: *mut leanh::LeanObject,
    mut v_lo_2439_: *mut leanh::LeanObject,
    mut v_hi_2440_: *mut leanh::LeanObject,
    mut v_w_2441_: *mut leanh::LeanObject,
    mut v_hlo_2442_: *mut leanh::LeanObject,
    mut v_hhi_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg(v_n_2437_, v_as_2438_, v_lo_2439_, v_hi_2440_);
    return v___x_2444_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___boxed(
    mut v_n_2445_: *mut leanh::LeanObject,
    mut v_as_2446_: *mut leanh::LeanObject,
    mut v_lo_2447_: *mut leanh::LeanObject,
    mut v_hi_2448_: *mut leanh::LeanObject,
    mut v_w_2449_: *mut leanh::LeanObject,
    mut v_hlo_2450_: *mut leanh::LeanObject,
    mut v_hhi_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2452_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3(v_n_2445_, v_as_2446_, v_lo_2447_, v_hi_2448_, v_w_2449_, v_hlo_2450_, v_hhi_2451_);
    leanh::lean_dec(v_hi_2448_);
    leanh::lean_dec(v_n_2445_);
    return v_res_2452_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(
    mut v_snd_2453_: *mut leanh::LeanObject,
    mut v_k_2454_: *mut leanh::LeanObject,
    mut v_t_2455_: *mut leanh::LeanObject,
    mut v_hl_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___redArg(v_snd_2453_, v_k_2454_, v_t_2455_);
    return v___x_2457_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5___boxed(
    mut v_snd_2458_: *mut leanh::LeanObject,
    mut v_k_2459_: *mut leanh::LeanObject,
    mut v_t_2460_: *mut leanh::LeanObject,
    mut v_hl_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__5(v_snd_2458_, v_k_2459_, v_t_2460_, v_hl_2461_);
    leanh::lean_dec_ref(v_snd_2458_);
    return v_res_2462_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(
    mut v_n_2463_: *mut leanh::LeanObject,
    mut v_lo_2464_: *mut leanh::LeanObject,
    mut v_hi_2465_: *mut leanh::LeanObject,
    mut v_hhi_2466_: *mut leanh::LeanObject,
    mut v_pivot_2467_: *mut leanh::LeanObject,
    mut v_as_2468_: *mut leanh::LeanObject,
    mut v_i_2469_: *mut leanh::LeanObject,
    mut v_k_2470_: *mut leanh::LeanObject,
    mut v_ilo_2471_: *mut leanh::LeanObject,
    mut v_ik_2472_: *mut leanh::LeanObject,
    mut v_w_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___redArg(v_hi_2465_, v_pivot_2467_, v_as_2468_, v_i_2469_, v_k_2470_);
    return v___x_2474_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5___boxed(
    mut v_n_2475_: *mut leanh::LeanObject,
    mut v_lo_2476_: *mut leanh::LeanObject,
    mut v_hi_2477_: *mut leanh::LeanObject,
    mut v_hhi_2478_: *mut leanh::LeanObject,
    mut v_pivot_2479_: *mut leanh::LeanObject,
    mut v_as_2480_: *mut leanh::LeanObject,
    mut v_i_2481_: *mut leanh::LeanObject,
    mut v_k_2482_: *mut leanh::LeanObject,
    mut v_ilo_2483_: *mut leanh::LeanObject,
    mut v_ik_2484_: *mut leanh::LeanObject,
    mut v_w_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3_spec__5(v_n_2475_, v_lo_2476_, v_hi_2477_, v_hhi_2478_, v_pivot_2479_, v_as_2480_, v_i_2481_, v_k_2482_, v_ilo_2483_, v_ik_2484_, v_w_2485_);
    leanh::lean_dec_ref(v_pivot_2479_);
    leanh::lean_dec(v_hi_2477_);
    leanh::lean_dec(v_lo_2476_);
    leanh::lean_dec(v_n_2475_);
    return v_res_2486_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(
    mut v_fst_2487_: *mut leanh::LeanObject,
    mut v_old_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_old_2488_) == 0 {
                    v___x_2493_ = l_Lean_NameSet_empty;
                    v___y_2490_ = v___x_2493_;
                    state = 1;
                    continue;
                } else {
                    v_val_2494_ = leanh::lean_ctor_get(v_old_2488_, 0);
                    leanh::lean_inc(v_val_2494_);
                    leanh::lean_dec_ref_known(v_old_2488_, 1);
                    v___y_2490_ = v_val_2494_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2491_ = l_Lean_NameSet_insert(v___y_2490_, v_fst_2487_);
                v___x_2492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2492_, 0, v___x_2491_);
                return v___x_2492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(
    mut v_fst_2495_: *mut leanh::LeanObject,
    mut v_k_2496_: *mut leanh::LeanObject,
    mut v_t_2497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut v_impl_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2517_: u8 = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2497_) == 0 {
                    v_size_2498_ = leanh::lean_ctor_get(v_t_2497_, 0);
                    v_k_2499_ = leanh::lean_ctor_get(v_t_2497_, 1);
                    v_v_2500_ = leanh::lean_ctor_get(v_t_2497_, 2);
                    v_l_2501_ = leanh::lean_ctor_get(v_t_2497_, 3);
                    v_r_2502_ = leanh::lean_ctor_get(v_t_2497_, 4);
                    v_isSharedCheck_2517_ = (!leanh::lean_is_exclusive(v_t_2497_)) as u8;
                    if v_isSharedCheck_2517_ == 0 {
                        v___x_2504_ = v_t_2497_;
                        v_isShared_2505_ = v_isSharedCheck_2517_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2502_);
                        leanh::lean_inc(v_l_2501_);
                        leanh::lean_inc(v_v_2500_);
                        leanh::lean_inc(v_k_2499_);
                        leanh::lean_inc(v_size_2498_);
                        leanh::lean_dec(v_t_2497_);
                        v___x_2504_ = leanh::lean_box(0);
                        v_isShared_2505_ = v_isSharedCheck_2517_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2518_ = leanh::lean_box(0);
                    v___x_2519_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_2495_, v___x_2518_);
                    v_val_2520_ = leanh::lean_ctor_get(v___x_2519_, 0);
                    leanh::lean_inc(v_val_2520_);
                    leanh::lean_dec(v___x_2519_);
                    v___x_2521_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2522_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_2522_, 0, v___x_2521_);
                    leanh::lean_ctor_set(v___x_2522_, 1, v_k_2496_);
                    leanh::lean_ctor_set(v___x_2522_, 2, v_val_2520_);
                    leanh::lean_ctor_set(v___x_2522_, 3, v_t_2497_);
                    leanh::lean_ctor_set(v___x_2522_, 4, v_t_2497_);
                    return v___x_2522_;
                }
            }
            1 => {
                v___x_2506_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2496_, v_k_2499_);
                match v___x_2506_ {
                    0 => {
                        leanh::lean_del_object(v___x_2504_);
                        leanh::lean_dec(v_size_2498_);
                        v_impl_2507_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_2495_, v_k_2496_, v_l_2501_);
                        v___x_2508_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_2499_,
                            v_v_2500_,
                            v_impl_2507_,
                            v_r_2502_,
                        );
                        return v___x_2508_;
                    }
                    1 => {
                        leanh::lean_dec(v_k_2499_);
                        v___x_2509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2509_, 0, v_v_2500_);
                        v___x_2510_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg___lam__0(v_fst_2495_, v___x_2509_);
                        v_val_2511_ = leanh::lean_ctor_get(v___x_2510_, 0);
                        leanh::lean_inc(v_val_2511_);
                        leanh::lean_dec(v___x_2510_);
                        if v_isShared_2505_ == 0 {
                            leanh::lean_ctor_set(v___x_2504_, 2, v_val_2511_);
                            leanh::lean_ctor_set(v___x_2504_, 1, v_k_2496_);
                            v___x_2513_ = v___x_2504_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2514_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_size_2498_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_k_2496_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_val_2511_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_l_2501_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_r_2502_);
                            v___x_2513_ = v_reuseFailAlloc_2514_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_del_object(v___x_2504_);
                        leanh::lean_dec(v_size_2498_);
                        v_impl_2515_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_2495_, v_k_2496_, v_r_2502_);
                        v___x_2516_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_2499_,
                            v_v_2500_,
                            v_l_2501_,
                            v_impl_2515_,
                        );
                        return v___x_2516_;
                    }
                }
            }
            2 => {
                return v___x_2513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(
    mut v_fst_2523_: *mut leanh::LeanObject,
    mut v_as_2524_: *mut leanh::LeanObject,
    mut v_i_2525_: usize,
    mut v_stop_2526_: usize,
    mut v_b_2527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: usize = 0;
    let mut v___x_2532_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2528_ = lean_usize_dec_eq(v_i_2525_, v_stop_2526_);
                if v___x_2528_ == 0 {
                    v___x_2529_ = lean_array_uget_borrowed(v_as_2524_, v_i_2525_);
                    leanh::lean_inc(v___x_2529_);
                    leanh::lean_inc(v_fst_2523_);
                    v___x_2530_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_2523_, v___x_2529_, v_b_2527_);
                    v___x_2531_ = 1usize;
                    v___x_2532_ = lean_usize_add(v_i_2525_, v___x_2531_);
                    v_i_2525_ = v___x_2532_;
                    v_b_2527_ = v___x_2530_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2523_);
                    return v_b_2527_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1___boxed(
    mut v_fst_2534_: *mut leanh::LeanObject,
    mut v_as_2535_: *mut leanh::LeanObject,
    mut v_i_2536_: *mut leanh::LeanObject,
    mut v_stop_2537_: *mut leanh::LeanObject,
    mut v_b_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2539_: usize = 0;
    let mut v_stop_boxed_2540_: usize = 0;
    let mut v_res_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2539_ = leanh::lean_unbox_usize(v_i_2536_);
    leanh::lean_dec(v_i_2536_);
    v_stop_boxed_2540_ = leanh::lean_unbox_usize(v_stop_2537_);
    leanh::lean_dec(v_stop_2537_);
    v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_2534_, v_as_2535_, v_i_boxed_2539_, v_stop_boxed_2540_, v_b_2538_);
    leanh::lean_dec_ref(v_as_2535_);
    return v_res_2541_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___lam__0(
    mut v_table_2542_: *mut leanh::LeanObject,
    mut v_x_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    v_fst_2544_ = leanh::lean_ctor_get(v_x_2543_, 0);
    leanh::lean_inc(v_fst_2544_);
    v_snd_2545_ = leanh::lean_ctor_get(v_x_2543_, 1);
    leanh::lean_inc(v_snd_2545_);
    leanh::lean_dec_ref(v_x_2543_);
    v___x_2546_ = leanh::lean_unsigned_to_nat(0);
    v___x_2547_ = lean_array_get_size(v_snd_2545_);
    v___x_2548_ = lean_nat_dec_lt(v___x_2546_, v___x_2547_);
    if v___x_2548_ == 0 {
        leanh::lean_dec(v_snd_2545_);
        leanh::lean_dec(v_fst_2544_);
        return v_table_2542_;
    } else {
        let mut v___x_2549_: u8 = 0;
        v___x_2549_ = lean_nat_dec_le(v___x_2547_, v___x_2547_);
        if v___x_2549_ == 0 {
            if v___x_2548_ == 0 {
                leanh::lean_dec(v_snd_2545_);
                leanh::lean_dec(v_fst_2544_);
                return v_table_2542_;
            } else {
                let mut v___x_2550_: usize = 0;
                let mut v___x_2551_: usize = 0;
                let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2550_ = 0usize;
                v___x_2551_ = lean_usize_of_nat(v___x_2547_);
                v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_2544_, v_snd_2545_, v___x_2550_, v___x_2551_, v_table_2542_);
                leanh::lean_dec(v_snd_2545_);
                return v___x_2552_;
            }
        } else {
            let mut v___x_2553_: usize = 0;
            let mut v___x_2554_: usize = 0;
            let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2553_ = 0usize;
            v___x_2554_ = lean_usize_of_nat(v___x_2547_);
            v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__1(v_fst_2544_, v_snd_2545_, v___x_2553_, v___x_2554_, v_table_2542_);
            leanh::lean_dec(v_snd_2545_);
            return v___x_2555_;
        }
    }
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting()
-> *mut leanh::LeanObject {
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2575_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___closed__4;
    v___x_2576_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2575_);
    return v___x_2576_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting___boxed(
    mut v_a_2577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2578_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
    return v_res_2578_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0(
    mut v_fst_2579_: *mut leanh::LeanObject,
    mut v_k_2580_: *mut leanh::LeanObject,
    mut v_t_2581_: *mut leanh::LeanObject,
    mut v_hl_2582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2583_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting_spec__0___redArg(v_fst_2579_, v_k_2580_, v_t_2581_);
    return v___x_2583_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2584_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2585_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_2586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2586_, 0, v___x_2585_);
    return v___x_2586_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_2588_ = leanh::lean_unsigned_to_nat(0);
    v___x_2589_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2589_, 0, v___x_2588_);
    leanh::lean_ctor_set(v___x_2589_, 1, v___x_2588_);
    leanh::lean_ctor_set(v___x_2589_, 2, v___x_2588_);
    leanh::lean_ctor_set(v___x_2589_, 3, v___x_2588_);
    leanh::lean_ctor_set(v___x_2589_, 4, v___x_2587_);
    leanh::lean_ctor_set(v___x_2589_, 5, v___x_2587_);
    leanh::lean_ctor_set(v___x_2589_, 6, v___x_2587_);
    leanh::lean_ctor_set(v___x_2589_, 7, v___x_2587_);
    leanh::lean_ctor_set(v___x_2589_, 8, v___x_2587_);
    leanh::lean_ctor_set(v___x_2589_, 9, v___x_2587_);
    return v___x_2589_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = leanh::lean_unsigned_to_nat(32);
    v___x_2591_ = lean_mk_empty_array_with_capacity(v___x_2590_);
    v___x_2592_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2592_, 0, v___x_2591_);
    return v___x_2592_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2593_: usize = 0;
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = 5usize;
    v___x_2594_ = leanh::lean_unsigned_to_nat(0);
    v___x_2595_ = leanh::lean_unsigned_to_nat(32);
    v___x_2596_ = lean_mk_empty_array_with_capacity(v___x_2595_);
    v___x_2597_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_2598_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2598_, 0, v___x_2597_);
    leanh::lean_ctor_set(v___x_2598_, 1, v___x_2596_);
    leanh::lean_ctor_set(v___x_2598_, 2, v___x_2594_);
    leanh::lean_ctor_set(v___x_2598_, 3, v___x_2594_);
    leanh::lean_ctor_set_usize(v___x_2598_, 4, v___x_2593_);
    return v___x_2598_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = leanh::lean_box(1);
    v___x_2600_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_2601_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_2602_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2602_, 0, v___x_2601_);
    leanh::lean_ctor_set(v___x_2602_, 1, v___x_2600_);
    leanh::lean_ctor_set(v___x_2602_, 2, v___x_2599_);
    return v___x_2602_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_2603_: *mut leanh::LeanObject,
    mut v___y_2604_: *mut leanh::LeanObject,
    mut v___y_2605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2607_ = lean_st_ref_get(v___y_2605_);
    v_env_2608_ = leanh::lean_ctor_get(v___x_2607_, 0);
    leanh::lean_inc_ref(v_env_2608_);
    leanh::lean_dec(v___x_2607_);
    v_options_2609_ = leanh::lean_ctor_get(v___y_2604_, 2);
    v___x_2610_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_2611_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_2609_);
    v___x_2612_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2612_, 0, v_env_2608_);
    leanh::lean_ctor_set(v___x_2612_, 1, v___x_2610_);
    leanh::lean_ctor_set(v___x_2612_, 2, v___x_2611_);
    leanh::lean_ctor_set(v___x_2612_, 3, v_options_2609_);
    v___x_2613_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2613_, 0, v___x_2612_);
    leanh::lean_ctor_set(v___x_2613_, 1, v_msgData_2603_);
    v___x_2614_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2614_, 0, v___x_2613_);
    return v___x_2614_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_2615_: *mut leanh::LeanObject,
    mut v___y_2616_: *mut leanh::LeanObject,
    mut v___y_2617_: *mut leanh::LeanObject,
    mut v___y_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2619_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2615_, v___y_2616_, v___y_2617_);
    leanh::lean_dec(v___y_2617_);
    leanh::lean_dec_ref(v___y_2616_);
    return v_res_2619_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_2620_: *mut leanh::LeanObject,
    mut v___y_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2624_ = leanh::lean_ctor_get(v___y_2621_, 5);
                v___x_2625_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0(v_msg_2620_, v___y_2621_, v___y_2622_);
                v_a_2626_ = leanh::lean_ctor_get(v___x_2625_, 0);
                v_isSharedCheck_2634_ = (!leanh::lean_is_exclusive(v___x_2625_)) as u8;
                if v_isSharedCheck_2634_ == 0 {
                    v___x_2628_ = v___x_2625_;
                    v_isShared_2629_ = v_isSharedCheck_2634_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2626_);
                    leanh::lean_dec(v___x_2625_);
                    v___x_2628_ = leanh::lean_box(0);
                    v_isShared_2629_ = v_isSharedCheck_2634_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2624_);
                v___x_2630_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2630_, 0, v_ref_2624_);
                leanh::lean_ctor_set(v___x_2630_, 1, v_a_2626_);
                if v_isShared_2629_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2628_, 1);
                    leanh::lean_ctor_set(v___x_2628_, 0, v___x_2630_);
                    v___x_2632_ = v___x_2628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_2635_: *mut leanh::LeanObject,
    mut v___y_2636_: *mut leanh::LeanObject,
    mut v___y_2637_: *mut leanh::LeanObject,
    mut v___y_2638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2639_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_2635_, v___y_2636_, v___y_2637_);
    leanh::lean_dec(v___y_2637_);
    leanh::lean_dec_ref(v___y_2636_);
    return v_res_2639_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__0;
    v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
    return v___x_2642_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__2;
    v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
    return v___x_2645_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2647_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__4;
    v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
    return v___x_2648_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(
    mut v_name_2652_: *mut leanh::LeanObject,
    mut v_kind_2653_: u8,
    mut v___y_2654_: *mut leanh::LeanObject,
    mut v___y_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2657_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__1);
                v___x_2658_ = l_Lean_MessageData_ofName(v_name_2652_);
                v___x_2659_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2659_, 0, v___x_2657_);
                leanh::lean_ctor_set(v___x_2659_, 1, v___x_2658_);
                v___x_2660_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__3);
                v___x_2661_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2661_, 0, v___x_2659_);
                leanh::lean_ctor_set(v___x_2661_, 1, v___x_2660_);
                match v_kind_2653_ {
                    0 => {
                        v___x_2670_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__6;
                        v___y_2663_ = v___x_2670_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2671_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__7;
                        v___y_2663_ = v___x_2671_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2672_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__8;
                        v___y_2663_ = v___x_2672_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_2663_);
                v___x_2664_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2664_, 0, v___y_2663_);
                v___x_2665_ = l_Lean_MessageData_ofFormat(v___x_2664_);
                v___x_2666_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2666_, 0, v___x_2661_);
                leanh::lean_ctor_set(v___x_2666_, 1, v___x_2665_);
                v___x_2667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
                v___x_2668_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2668_, 0, v___x_2666_);
                leanh::lean_ctor_set(v___x_2668_, 1, v___x_2667_);
                v___x_2669_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_2668_, v___y_2654_, v___y_2655_);
                return v___x_2669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_name_2673_: *mut leanh::LeanObject,
    mut v_kind_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
    mut v___y_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_2678_: u8 = 0;
    let mut v_res_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2678_ = (leanh::lean_unbox(v_kind_2674_) as u8);
    v_res_2679_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_2673_, v_kind_boxed_2678_, v___y_2675_, v___y_2676_);
    leanh::lean_dec(v___y_2676_);
    leanh::lean_dec_ref(v___y_2675_);
    return v_res_2679_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(
    mut v_sz_2680_: usize,
    mut v_i_2681_: usize,
    mut v_bs_2682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2683_: u8 = 0;
    let mut v_v_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: usize = 0;
    let mut v___x_2689_: usize = 0;
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2683_ = lean_usize_dec_lt(v_i_2681_, v_sz_2680_);
                if v___x_2683_ == 0 {
                    return v_bs_2682_;
                } else {
                    v_v_2684_ = lean_array_uget(v_bs_2682_, v_i_2681_);
                    v___x_2685_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2686_ = lean_array_uset(v_bs_2682_, v_i_2681_, v___x_2685_);
                    v___x_2687_ = l_Lean_Syntax_getId(v_v_2684_);
                    leanh::lean_dec(v_v_2684_);
                    v___x_2688_ = 1usize;
                    v___x_2689_ = lean_usize_add(v_i_2681_, v___x_2688_);
                    v___x_2690_ = lean_array_uset(v_bs_x27_2686_, v_i_2681_, v___x_2687_);
                    v_i_2681_ = v___x_2689_;
                    v_bs_2682_ = v___x_2690_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1___boxed(
    mut v_sz_2692_: *mut leanh::LeanObject,
    mut v_i_2693_: *mut leanh::LeanObject,
    mut v_bs_2694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2695_: usize = 0;
    let mut v_i_boxed_2696_: usize = 0;
    let mut v_res_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2695_ = leanh::lean_unbox_usize(v_sz_2692_);
    leanh::lean_dec(v_sz_2692_);
    v_i_boxed_2696_ = leanh::lean_unbox_usize(v_i_2693_);
    leanh::lean_dec(v_i_2693_);
    v_res_2697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_boxed_2695_, v_i_boxed_2696_, v_bs_2694_);
    return v_res_2697_;
}
pub unsafe fn _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2698_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2698_;
}
pub unsafe fn _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2699_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once), _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
    v___x_2700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2700_, 0, v___x_2699_);
    return v___x_2700_;
}
pub unsafe fn _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once), _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
    v___x_2702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2702_, 0, v___x_2701_);
    leanh::lean_ctor_set(v___x_2702_, 1, v___x_2701_);
    return v___x_2702_;
}
pub unsafe fn _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2704_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
    v___x_2705_ = l_Lean_stringToMessageData(v___x_2704_);
    return v___x_2705_;
}
pub unsafe fn _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2707_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__5_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
    v___x_2708_ = l_Lean_stringToMessageData(v___x_2707_);
    return v___x_2708_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v___x_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v___x_2716_: *mut leanh::LeanObject,
    mut v___x_2717_: *mut leanh::LeanObject,
    mut v___x_2718_: *mut leanh::LeanObject,
    mut v___x_2719_: *mut leanh::LeanObject,
    mut v_decl_2720_: *mut leanh::LeanObject,
    mut v_stx_2721_: *mut leanh::LeanObject,
    mut v_kind_2722_: u8,
    mut v___y_2723_: *mut leanh::LeanObject,
    mut v___y_2724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v_asyncMode_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2743_: usize = 0;
    let mut v___x_2744_: usize = 0;
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v_asyncMode_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2773_: u8 = 0;
    let mut v_unused_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v_unused_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_altSyntaxIds_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: u8 = 0;
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2796_: u8 = 0;
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2800_: u8 = 0;
    let mut v_kind_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: u8 = 0;
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: u8 = 0;
    let mut v_pre_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2860_ = 0;
                v___x_2861_ = l_Lean_instBEqAttributeKind_beq(v_kind_2722_, v___x_2860_);
                if v___x_2861_ == 0 {
                    leanh::lean_dec(v_stx_2721_);
                    leanh::lean_dec(v_decl_2720_);
                    leanh::lean_dec_ref(v_a_2715_);
                    leanh::lean_dec(v___x_2714_);
                    leanh::lean_dec_ref(v_a_2713_);
                    v___x_2862_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v___x_2719_, v_kind_2722_, v___y_2723_, v___y_2724_);
                    return v___x_2862_;
                } else {
                    leanh::lean_dec(v___x_2719_);
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2729_ = lean_st_ref_take(v___y_2728_);
                v_toEnvExtension_2730_ = leanh::lean_ctor_get(v_a_2713_, 0);
                v_env_2731_ = leanh::lean_ctor_get(v___x_2729_, 0);
                v_nextMacroScope_2732_ = leanh::lean_ctor_get(v___x_2729_, 1);
                v_ngen_2733_ = leanh::lean_ctor_get(v___x_2729_, 2);
                v_auxDeclNGen_2734_ = leanh::lean_ctor_get(v___x_2729_, 3);
                v_traceState_2735_ = leanh::lean_ctor_get(v___x_2729_, 4);
                v_messages_2736_ = leanh::lean_ctor_get(v___x_2729_, 6);
                v_infoState_2737_ = leanh::lean_ctor_get(v___x_2729_, 7);
                v_snapshotTasks_2738_ = leanh::lean_ctor_get(v___x_2729_, 8);
                v_isSharedCheck_2776_ = (!leanh::lean_is_exclusive(v___x_2729_)) as u8;
                if v_isSharedCheck_2776_ == 0 {
                    v_unused_2777_ = leanh::lean_ctor_get(v___x_2729_, 5);
                    leanh::lean_dec(v_unused_2777_);
                    v___x_2740_ = v___x_2729_;
                    v_isShared_2741_ = v_isSharedCheck_2776_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2738_);
                    leanh::lean_inc(v_infoState_2737_);
                    leanh::lean_inc(v_messages_2736_);
                    leanh::lean_inc(v_traceState_2735_);
                    leanh::lean_inc(v_auxDeclNGen_2734_);
                    leanh::lean_inc(v_ngen_2733_);
                    leanh::lean_inc(v_nextMacroScope_2732_);
                    leanh::lean_inc(v_env_2731_);
                    leanh::lean_dec(v___x_2729_);
                    v___x_2740_ = leanh::lean_box(0);
                    v_isShared_2741_ = v_isSharedCheck_2776_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_2742_ = leanh::lean_ctor_get(v_toEnvExtension_2730_, 2);
                leanh::lean_inc(v_asyncMode_2742_);
                v_sz_2743_ = lean_array_size(v___y_2727_);
                v___x_2744_ = 0usize;
                v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__1(v_sz_2743_, v___x_2744_, v___y_2727_);
                v___x_2746_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2746_, 0, v_decl_2720_);
                leanh::lean_ctor_set(v___x_2746_, 1, v___x_2745_);
                leanh::lean_inc(v___x_2714_);
                leanh::lean_inc_ref(v___x_2746_);
                v___x_2747_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_a_2713_,
                    v_env_2731_,
                    v___x_2746_,
                    v_asyncMode_2742_,
                    v___x_2714_,
                );
                leanh::lean_dec(v_asyncMode_2742_);
                v___x_2748_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once), _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
                if v_isShared_2741_ == 0 {
                    leanh::lean_ctor_set(v___x_2740_, 5, v___x_2748_);
                    leanh::lean_ctor_set(v___x_2740_, 0, v___x_2747_);
                    v___x_2750_ = v___x_2740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_nextMacroScope_2732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_ngen_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_auxDeclNGen_2734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_traceState_2735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 5, v___x_2748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 6, v_messages_2736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 7, v_infoState_2737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 8, v_snapshotTasks_2738_);
                    v___x_2750_ = v_reuseFailAlloc_2775_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2751_ = lean_st_ref_set(v___y_2728_, v___x_2750_);
                v___x_2752_ = lean_st_ref_take(v___y_2728_);
                v_toEnvExtension_2753_ = leanh::lean_ctor_get(v_a_2715_, 0);
                v_env_2754_ = leanh::lean_ctor_get(v___x_2752_, 0);
                v_nextMacroScope_2755_ = leanh::lean_ctor_get(v___x_2752_, 1);
                v_ngen_2756_ = leanh::lean_ctor_get(v___x_2752_, 2);
                v_auxDeclNGen_2757_ = leanh::lean_ctor_get(v___x_2752_, 3);
                v_traceState_2758_ = leanh::lean_ctor_get(v___x_2752_, 4);
                v_messages_2759_ = leanh::lean_ctor_get(v___x_2752_, 6);
                v_infoState_2760_ = leanh::lean_ctor_get(v___x_2752_, 7);
                v_snapshotTasks_2761_ = leanh::lean_ctor_get(v___x_2752_, 8);
                v_isSharedCheck_2773_ = (!leanh::lean_is_exclusive(v___x_2752_)) as u8;
                if v_isSharedCheck_2773_ == 0 {
                    v_unused_2774_ = leanh::lean_ctor_get(v___x_2752_, 5);
                    leanh::lean_dec(v_unused_2774_);
                    v___x_2763_ = v___x_2752_;
                    v_isShared_2764_ = v_isSharedCheck_2773_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2761_);
                    leanh::lean_inc(v_infoState_2760_);
                    leanh::lean_inc(v_messages_2759_);
                    leanh::lean_inc(v_traceState_2758_);
                    leanh::lean_inc(v_auxDeclNGen_2757_);
                    leanh::lean_inc(v_ngen_2756_);
                    leanh::lean_inc(v_nextMacroScope_2755_);
                    leanh::lean_inc(v_env_2754_);
                    leanh::lean_dec(v___x_2752_);
                    v___x_2763_ = leanh::lean_box(0);
                    v_isShared_2764_ = v_isSharedCheck_2773_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_asyncMode_2765_ = leanh::lean_ctor_get(v_toEnvExtension_2753_, 2);
                leanh::lean_inc(v_asyncMode_2765_);
                v___x_2766_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_a_2715_,
                    v_env_2754_,
                    v___x_2746_,
                    v_asyncMode_2765_,
                    v___x_2714_,
                );
                leanh::lean_dec(v_asyncMode_2765_);
                if v_isShared_2764_ == 0 {
                    leanh::lean_ctor_set(v___x_2763_, 5, v___x_2748_);
                    leanh::lean_ctor_set(v___x_2763_, 0, v___x_2766_);
                    v___x_2768_ = v___x_2763_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2772_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_nextMacroScope_2755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_ngen_2756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 3, v_auxDeclNGen_2757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 4, v_traceState_2758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 5, v___x_2748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 6, v_messages_2759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 7, v_infoState_2760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 8, v_snapshotTasks_2761_);
                    v___x_2768_ = v_reuseFailAlloc_2772_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2769_ = lean_st_ref_set(v___y_2728_, v___x_2768_);
                v___x_2770_ = leanh::lean_box(0);
                v___x_2771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2771_, 0, v___x_2770_);
                return v___x_2771_;
            }
            6 => {
                v___x_2782_ = l_Lean_isPrivateName(v_decl_2720_);
                if v___x_2782_ == 0 {
                    v___y_2727_ = v_altSyntaxIds_2779_;
                    v___y_2728_ = v___y_2781_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_altSyntaxIds_2779_);
                    leanh::lean_dec(v_decl_2720_);
                    leanh::lean_dec_ref(v_a_2715_);
                    leanh::lean_dec(v___x_2714_);
                    leanh::lean_dec_ref(v_a_2713_);
                    v___x_2783_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once), _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__4_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
                    v___x_2784_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_2783_, v___y_2780_, v___y_2781_);
                    return v___x_2784_;
                }
            }
            7 => {
                v___x_2788_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once), _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__6_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
                v___x_2789_ = l_Lean_Syntax_instRepr_repr(v_stx_2721_, v___x_2716_);
                v___x_2790_ = l_Lean_MessageData_ofFormat(v___x_2789_);
                v___x_2791_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2791_, 0, v___x_2788_);
                leanh::lean_ctor_set(v___x_2791_, 1, v___x_2790_);
                v___x_2792_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_2791_, v___y_2786_, v___y_2787_);
                v_a_2793_ = leanh::lean_ctor_get(v___x_2792_, 0);
                v_isSharedCheck_2800_ = (!leanh::lean_is_exclusive(v___x_2792_)) as u8;
                if v_isSharedCheck_2800_ == 0 {
                    v___x_2795_ = v___x_2792_;
                    v_isShared_2796_ = v_isSharedCheck_2800_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2793_);
                    leanh::lean_dec(v___x_2792_);
                    v___x_2795_ = leanh::lean_box(0);
                    v_isShared_2796_ = v_isSharedCheck_2800_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2796_ == 0 {
                    v___x_2798_ = v___x_2795_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
                    v___x_2798_ = v_reuseFailAlloc_2799_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2798_;
            }
            10 => {
                if leanh::lean_obj_tag(v_stx_2721_) == 1 {
                    v_kind_2802_ = leanh::lean_ctor_get(v_stx_2721_, 1);
                    if leanh::lean_obj_tag(v_kind_2802_) == 1 {
                        v_pre_2803_ = leanh::lean_ctor_get(v_kind_2802_, 0);
                        if leanh::lean_obj_tag(v_pre_2803_) == 1 {
                            v_pre_2804_ = leanh::lean_ctor_get(v_pre_2803_, 0);
                            match leanh::lean_obj_tag(v_pre_2804_) {
                                0 => {
                                    v_args_2805_ = leanh::lean_ctor_get(v_stx_2721_, 2);
                                    v_str_2806_ = leanh::lean_ctor_get(v_kind_2802_, 1);
                                    v_str_2807_ = leanh::lean_ctor_get(v_pre_2803_, 1);
                                    v___x_2808_ = lean_string_dec_eq(v_str_2807_, v___x_2717_);
                                    if v___x_2808_ == 0 {
                                        leanh::lean_dec(v_decl_2720_);
                                        leanh::lean_dec_ref(v_a_2715_);
                                        leanh::lean_dec(v___x_2714_);
                                        leanh::lean_dec_ref(v_a_2713_);
                                        v___y_2786_ = v___y_2723_;
                                        v___y_2787_ = v___y_2724_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_2809_ = lean_string_dec_eq(v_str_2806_, v___x_2718_);
                                        if v___x_2809_ == 0 {
                                            leanh::lean_dec(v_decl_2720_);
                                            leanh::lean_dec_ref(v_a_2715_);
                                            leanh::lean_dec(v___x_2714_);
                                            leanh::lean_dec_ref(v_a_2713_);
                                            v___y_2786_ = v___y_2723_;
                                            v___y_2787_ = v___y_2724_;
                                            state = 7;
                                            continue;
                                        } else {
                                            v___x_2810_ = lean_array_get_size(v_args_2805_);
                                            v___x_2811_ = leanh::lean_unsigned_to_nat(2);
                                            v___x_2812_ = lean_nat_dec_eq(v___x_2810_, v___x_2811_);
                                            if v___x_2812_ == 0 {
                                                leanh::lean_dec(v_decl_2720_);
                                                leanh::lean_dec_ref(v_a_2715_);
                                                leanh::lean_dec(v___x_2714_);
                                                leanh::lean_dec_ref(v_a_2713_);
                                                v___y_2786_ = v___y_2723_;
                                                v___y_2787_ = v___y_2724_;
                                                state = 7;
                                                continue;
                                            } else {
                                                v___x_2813_ = lean_array_fget_borrowed(
                                                    v_args_2805_,
                                                    v___x_2716_,
                                                );
                                                if leanh::lean_obj_tag(v___x_2813_) == 2 {
                                                    v_val_2814_ =
                                                        leanh::lean_ctor_get(v___x_2813_, 1);
                                                    v___x_2815_ = lean_string_dec_eq(
                                                        v_val_2814_,
                                                        v___x_2718_,
                                                    );
                                                    if v___x_2815_ == 0 {
                                                        leanh::lean_dec(v_decl_2720_);
                                                        leanh::lean_dec_ref(v_a_2715_);
                                                        leanh::lean_dec(v___x_2714_);
                                                        leanh::lean_dec_ref(v_a_2713_);
                                                        v___y_2786_ = v___y_2723_;
                                                        v___y_2787_ = v___y_2724_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        v___x_2816_ =
                                                            leanh::lean_unsigned_to_nat(1);
                                                        v___x_2817_ = lean_array_fget_borrowed(
                                                            v_args_2805_,
                                                            v___x_2816_,
                                                        );
                                                        if leanh::lean_obj_tag(v___x_2817_)
                                                            == 1
                                                        {
                                                            v_kind_2818_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_2817_,
                                                                    1,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v_kind_2818_,
                                                            ) == 1
                                                            {
                                                                v_pre_2819_ =
                                                                    leanh::lean_ctor_get(
                                                                        v_kind_2818_,
                                                                        0,
                                                                    );
                                                                if leanh::lean_obj_tag(
                                                                    v_pre_2819_,
                                                                ) == 0
                                                                {
                                                                    v_args_2820_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_2817_,
                                                                            2,
                                                                        );
                                                                    v_str_2821_ =
                                                                        leanh::lean_ctor_get(
                                                                            v_kind_2818_,
                                                                            1,
                                                                        );
                                                                    v___x_2822_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                                                                    v___x_2823_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_2821_,
                                                                            v___x_2822_,
                                                                        );
                                                                    if v___x_2823_ == 0 {
                                                                        leanh::lean_dec(
                                                                            v_decl_2720_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_a_2715_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_2714_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_a_2713_,
                                                                        );
                                                                        v___y_2786_ = v___y_2723_;
                                                                        v___y_2787_ = v___y_2724_;
                                                                        state = 7;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc_ref(
                                                                            v_args_2820_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v_stx_2721_, 3);
                                                                        v_altSyntaxIds_2779_ =
                                                                            v_args_2820_;
                                                                        v___y_2780_ = v___y_2723_;
                                                                        v___y_2781_ = v___y_2724_;
                                                                        state = 6;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_decl_2720_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_a_2715_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_2714_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_a_2713_,
                                                                    );
                                                                    v___y_2786_ = v___y_2723_;
                                                                    v___y_2787_ = v___y_2724_;
                                                                    state = 7;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec(
                                                                    v_decl_2720_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_a_2715_,
                                                                );
                                                                leanh::lean_dec(v___x_2714_);
                                                                leanh::lean_dec_ref(
                                                                    v_a_2713_,
                                                                );
                                                                v___y_2786_ = v___y_2723_;
                                                                v___y_2787_ = v___y_2724_;
                                                                state = 7;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_decl_2720_);
                                                            leanh::lean_dec_ref(v_a_2715_);
                                                            leanh::lean_dec(v___x_2714_);
                                                            leanh::lean_dec_ref(v_a_2713_);
                                                            v___y_2786_ = v___y_2723_;
                                                            v___y_2787_ = v___y_2724_;
                                                            state = 7;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_decl_2720_);
                                                    leanh::lean_dec_ref(v_a_2715_);
                                                    leanh::lean_dec(v___x_2714_);
                                                    leanh::lean_dec_ref(v_a_2713_);
                                                    v___y_2786_ = v___y_2723_;
                                                    v___y_2787_ = v___y_2724_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                                1 => {
                                    v_pre_2824_ = leanh::lean_ctor_get(v_pre_2804_, 0);
                                    if leanh::lean_obj_tag(v_pre_2824_) == 1 {
                                        v_pre_2825_ = leanh::lean_ctor_get(v_pre_2824_, 0);
                                        if leanh::lean_obj_tag(v_pre_2825_) == 0 {
                                            v_args_2826_ =
                                                leanh::lean_ctor_get(v_stx_2721_, 2);
                                            v_str_2827_ =
                                                leanh::lean_ctor_get(v_kind_2802_, 1);
                                            v_str_2828_ =
                                                leanh::lean_ctor_get(v_pre_2803_, 1);
                                            v_str_2829_ =
                                                leanh::lean_ctor_get(v_pre_2804_, 1);
                                            v_str_2830_ =
                                                leanh::lean_ctor_get(v_pre_2824_, 1);
                                            v___x_2831_ =
                                                lean_string_dec_eq(v_str_2830_, v___x_2717_);
                                            if v___x_2831_ == 0 {
                                                leanh::lean_dec(v_decl_2720_);
                                                leanh::lean_dec_ref(v_a_2715_);
                                                leanh::lean_dec(v___x_2714_);
                                                leanh::lean_dec_ref(v_a_2713_);
                                                v___y_2786_ = v___y_2723_;
                                                v___y_2787_ = v___y_2724_;
                                                state = 7;
                                                continue;
                                            } else {
                                                v___x_2832_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__8_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                                                v___x_2833_ =
                                                    lean_string_dec_eq(v_str_2829_, v___x_2832_);
                                                if v___x_2833_ == 0 {
                                                    leanh::lean_dec(v_decl_2720_);
                                                    leanh::lean_dec_ref(v_a_2715_);
                                                    leanh::lean_dec(v___x_2714_);
                                                    leanh::lean_dec_ref(v_a_2713_);
                                                    v___y_2786_ = v___y_2723_;
                                                    v___y_2787_ = v___y_2724_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    v___x_2834_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                                                    v___x_2835_ = lean_string_dec_eq(
                                                        v_str_2828_,
                                                        v___x_2834_,
                                                    );
                                                    if v___x_2835_ == 0 {
                                                        leanh::lean_dec(v_decl_2720_);
                                                        leanh::lean_dec_ref(v_a_2715_);
                                                        leanh::lean_dec(v___x_2714_);
                                                        leanh::lean_dec_ref(v_a_2713_);
                                                        v___y_2786_ = v___y_2723_;
                                                        v___y_2787_ = v___y_2724_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        v___x_2836_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                                                        v___x_2837_ = lean_string_dec_eq(
                                                            v_str_2827_,
                                                            v___x_2836_,
                                                        );
                                                        if v___x_2837_ == 0 {
                                                            leanh::lean_dec(v_decl_2720_);
                                                            leanh::lean_dec_ref(v_a_2715_);
                                                            leanh::lean_dec(v___x_2714_);
                                                            leanh::lean_dec_ref(v_a_2713_);
                                                            v___y_2786_ = v___y_2723_;
                                                            v___y_2787_ = v___y_2724_;
                                                            state = 7;
                                                            continue;
                                                        } else {
                                                            v___x_2838_ =
                                                                lean_array_get_size(v_args_2826_);
                                                            v___x_2839_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    2,
                                                                );
                                                            v___x_2840_ = lean_nat_dec_eq(
                                                                v___x_2838_,
                                                                v___x_2839_,
                                                            );
                                                            if v___x_2840_ == 0 {
                                                                leanh::lean_dec(
                                                                    v_decl_2720_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_a_2715_,
                                                                );
                                                                leanh::lean_dec(v___x_2714_);
                                                                leanh::lean_dec_ref(
                                                                    v_a_2713_,
                                                                );
                                                                v___y_2786_ = v___y_2723_;
                                                                v___y_2787_ = v___y_2724_;
                                                                state = 7;
                                                                continue;
                                                            } else {
                                                                v___x_2841_ =
                                                                    lean_array_fget_borrowed(
                                                                        v_args_2826_,
                                                                        v___x_2716_,
                                                                    );
                                                                if leanh::lean_obj_tag(
                                                                    v___x_2841_,
                                                                ) == 3
                                                                {
                                                                    v_val_2842_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_2841_,
                                                                            2,
                                                                        );
                                                                    if leanh::lean_obj_tag(
                                                                        v_val_2842_,
                                                                    ) == 1
                                                                    {
                                                                        v_pre_2843_ = leanh::lean_ctor_get(v_val_2842_, 0);
                                                                        if leanh::lean_obj_tag(v_pre_2843_) == 0 {
v_preresolved_2844_ = leanh::lean_ctor_get(v___x_2841_, 3);
v_str_2845_ = leanh::lean_ctor_get(v_val_2842_, 1);
v___x_2846_ = lean_string_dec_eq(v_str_2845_, v___x_2718_);
if v___x_2846_ == 0 {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
} else {
if leanh::lean_obj_tag(v_preresolved_2844_) == 0 {
v___x_2847_ = leanh::lean_unsigned_to_nat(1);
v___x_2848_ = lean_array_fget_borrowed(v_args_2826_, v___x_2847_);
if leanh::lean_obj_tag(v___x_2848_) == 1 {
v_kind_2849_ = leanh::lean_ctor_get(v___x_2848_, 1);
if leanh::lean_obj_tag(v_kind_2849_) == 1 {
v_pre_2850_ = leanh::lean_ctor_get(v_kind_2849_, 0);
if leanh::lean_obj_tag(v_pre_2850_) == 0 {
v_args_2851_ = leanh::lean_ctor_get(v___x_2848_, 2);
v_str_2852_ = leanh::lean_ctor_get(v_kind_2849_, 1);
v___x_2853_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0___closed__7_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
v___x_2854_ = lean_string_dec_eq(v_str_2852_, v___x_2853_);
if v___x_2854_ == 0 {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
} else {
v___x_2855_ = lean_array_get_size(v_args_2851_);
v___x_2856_ = lean_nat_dec_eq(v___x_2855_, v___x_2847_);
if v___x_2856_ == 0 {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
} else {
leanh::lean_inc_ref(v_args_2851_);
leanh::lean_dec_ref_known(v_stx_2721_, 3);
v___x_2857_ = lean_array_fget(v_args_2851_, v___x_2716_);
leanh::lean_dec_ref(v_args_2851_);
v___x_2858_ = lean_mk_empty_array_with_capacity(v___x_2847_);
v___x_2859_ = lean_array_push(v___x_2858_, v___x_2857_);
v_altSyntaxIds_2779_ = v___x_2859_;
v___y_2780_ = v___y_2723_;
v___y_2781_ = v___y_2724_;
state = 6; continue;
}
}
} else {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
}
} else {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
}
} else {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
}
} else {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
}
}
} else {
leanh::lean_dec(v_decl_2720_);
leanh::lean_dec_ref(v_a_2715_);
leanh::lean_dec(v___x_2714_);
leanh::lean_dec_ref(v_a_2713_);
v___y_2786_ = v___y_2723_;
v___y_2787_ = v___y_2724_;
state = 7; continue;
}
                                                                    } else {
                                                                        leanh::lean_dec(
                                                                            v_decl_2720_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_a_2715_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_2714_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_a_2713_,
                                                                        );
                                                                        v___y_2786_ = v___y_2723_;
                                                                        v___y_2787_ = v___y_2724_;
                                                                        state = 7;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_decl_2720_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_a_2715_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_2714_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_a_2713_,
                                                                    );
                                                                    v___y_2786_ = v___y_2723_;
                                                                    v___y_2787_ = v___y_2724_;
                                                                    state = 7;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_decl_2720_);
                                            leanh::lean_dec_ref(v_a_2715_);
                                            leanh::lean_dec(v___x_2714_);
                                            leanh::lean_dec_ref(v_a_2713_);
                                            v___y_2786_ = v___y_2723_;
                                            v___y_2787_ = v___y_2724_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_decl_2720_);
                                        leanh::lean_dec_ref(v_a_2715_);
                                        leanh::lean_dec(v___x_2714_);
                                        leanh::lean_dec_ref(v_a_2713_);
                                        v___y_2786_ = v___y_2723_;
                                        v___y_2787_ = v___y_2724_;
                                        state = 7;
                                        continue;
                                    }
                                }
                                _ => {
                                    leanh::lean_dec(v_decl_2720_);
                                    leanh::lean_dec_ref(v_a_2715_);
                                    leanh::lean_dec(v___x_2714_);
                                    leanh::lean_dec_ref(v_a_2713_);
                                    v___y_2786_ = v___y_2723_;
                                    v___y_2787_ = v___y_2724_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_decl_2720_);
                            leanh::lean_dec_ref(v_a_2715_);
                            leanh::lean_dec(v___x_2714_);
                            leanh::lean_dec_ref(v_a_2713_);
                            v___y_2786_ = v___y_2723_;
                            v___y_2787_ = v___y_2724_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_decl_2720_);
                        leanh::lean_dec_ref(v_a_2715_);
                        leanh::lean_dec(v___x_2714_);
                        leanh::lean_dec_ref(v_a_2713_);
                        v___y_2786_ = v___y_2723_;
                        v___y_2787_ = v___y_2724_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_decl_2720_);
                    leanh::lean_dec_ref(v_a_2715_);
                    leanh::lean_dec(v___x_2714_);
                    leanh::lean_dec_ref(v_a_2713_);
                    v___y_2786_ = v___y_2723_;
                    v___y_2787_ = v___y_2724_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(
    mut v_a_2863_: *mut leanh::LeanObject,
    mut v___x_2864_: *mut leanh::LeanObject,
    mut v_a_2865_: *mut leanh::LeanObject,
    mut v___x_2866_: *mut leanh::LeanObject,
    mut v___x_2867_: *mut leanh::LeanObject,
    mut v___x_2868_: *mut leanh::LeanObject,
    mut v___x_2869_: *mut leanh::LeanObject,
    mut v_decl_2870_: *mut leanh::LeanObject,
    mut v_stx_2871_: *mut leanh::LeanObject,
    mut v_kind_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_2876_: u8 = 0;
    let mut v_res_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2876_ = (leanh::lean_unbox(v_kind_2872_) as u8);
    v_res_2877_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v_a_2863_, v___x_2864_, v_a_2865_, v___x_2866_, v___x_2867_, v___x_2868_, v___x_2869_, v_decl_2870_, v_stx_2871_, v_kind_boxed_2876_, v___y_2873_, v___y_2874_);
    leanh::lean_dec(v___y_2874_);
    leanh::lean_dec_ref(v___y_2873_);
    leanh::lean_dec_ref(v___x_2868_);
    leanh::lean_dec_ref(v___x_2867_);
    leanh::lean_dec(v___x_2866_);
    return v_res_2877_;
}
pub unsafe fn _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2879_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
    v___x_2880_ = l_Lean_stringToMessageData(v___x_2879_);
    return v___x_2880_;
}
pub unsafe fn _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
    v___x_2883_ = l_Lean_stringToMessageData(v___x_2882_);
    return v___x_2883_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(
    mut v___x_2884_: *mut leanh::LeanObject,
    mut v_decl_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2889_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once), _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
    v___x_2890_ = l_Lean_MessageData_ofName(v___x_2884_);
    v___x_2891_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2891_, 0, v___x_2889_);
    leanh::lean_ctor_set(v___x_2891_, 1, v___x_2890_);
    v___x_2892_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__once), _init_l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_);
    v___x_2893_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2893_, 0, v___x_2891_);
    leanh::lean_ctor_set(v___x_2893_, 1, v___x_2892_);
    v___x_2894_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v___x_2893_, v___y_2886_, v___y_2887_);
    return v___x_2894_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(
    mut v___x_2895_: *mut leanh::LeanObject,
    mut v_decl_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2900_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__1_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_(v___x_2895_, v_decl_2896_, v___y_2897_, v___y_2898_);
    leanh::lean_dec(v___y_2898_);
    leanh::lean_dec_ref(v___y_2897_);
    leanh::lean_dec(v_decl_2896_);
    return v_res_2900_;
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_unused_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v_a_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2972_: u8 = 0;
    let mut v_a_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2976_: u8 = 0;
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2934_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect();
                if leanh::lean_obj_tag(v___x_2934_) == 0 {
                    v_a_2935_ = leanh::lean_ctor_get(v___x_2934_, 0);
                    leanh::lean_inc(v_a_2935_);
                    leanh::lean_dec_ref_known(v___x_2934_, 1);
                    v___x_2936_ =
                        l___private_Lean_IdentifierSuggestion_0__Lean_mkIncorrectToExisting();
                    if leanh::lean_obj_tag(v___x_2936_) == 0 {
                        v_a_2937_ = leanh::lean_ctor_get(v___x_2936_, 0);
                        leanh::lean_inc_n(v_a_2937_, 2);
                        leanh::lean_dec_ref_known(v___x_2936_, 1);
                        v___x_2938_ = leanh::lean_box(0);
                        v___x_2939_ = l___private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect___closed__4;
                        v___x_2940_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2941_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__9_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                        v___x_2942_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__10_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                        leanh::lean_inc(v_a_2935_);
                        v___f_2943_ = leanh::lean_alloc_closure(l___private_Lean_IdentifierSuggestion_0__Lean_initFn___lam__0_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 13, 7);
                        leanh::lean_closure_set(v___f_2943_, 0, v_a_2935_);
                        leanh::lean_closure_set(v___f_2943_, 1, v___x_2938_);
                        leanh::lean_closure_set(v___f_2943_, 2, v_a_2937_);
                        leanh::lean_closure_set(v___f_2943_, 3, v___x_2940_);
                        leanh::lean_closure_set(v___f_2943_, 4, v___x_2939_);
                        leanh::lean_closure_set(v___f_2943_, 5, v___x_2941_);
                        leanh::lean_closure_set(v___f_2943_, 6, v___x_2942_);
                        v___f_2944_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__11_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                        v___x_2945_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn___closed__13_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_;
                        v___x_2946_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2946_, 0, v___x_2945_);
                        leanh::lean_ctor_set(v___x_2946_, 1, v___f_2943_);
                        leanh::lean_ctor_set(v___x_2946_, 2, v___f_2944_);
                        v___x_2947_ = l_Lean_registerBuiltinAttribute(v___x_2946_);
                        if leanh::lean_obj_tag(v___x_2947_) == 0 {
                            v_isSharedCheck_2955_ =
                                (!leanh::lean_is_exclusive(v___x_2947_)) as u8;
                            if v_isSharedCheck_2955_ == 0 {
                                v_unused_2956_ = leanh::lean_ctor_get(v___x_2947_, 0);
                                leanh::lean_dec(v_unused_2956_);
                                v___x_2949_ = v___x_2947_;
                                v_isShared_2950_ = v_isSharedCheck_2955_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2947_);
                                v___x_2949_ = leanh::lean_box(0);
                                v_isShared_2950_ = v_isSharedCheck_2955_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2937_);
                            leanh::lean_dec(v_a_2935_);
                            v_a_2957_ = leanh::lean_ctor_get(v___x_2947_, 0);
                            v_isSharedCheck_2964_ =
                                (!leanh::lean_is_exclusive(v___x_2947_)) as u8;
                            if v_isSharedCheck_2964_ == 0 {
                                v___x_2959_ = v___x_2947_;
                                v_isShared_2960_ = v_isSharedCheck_2964_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2957_);
                                leanh::lean_dec(v___x_2947_);
                                v___x_2959_ = leanh::lean_box(0);
                                v_isShared_2960_ = v_isSharedCheck_2964_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2935_);
                        v_a_2965_ = leanh::lean_ctor_get(v___x_2936_, 0);
                        v_isSharedCheck_2972_ =
                            (!leanh::lean_is_exclusive(v___x_2936_)) as u8;
                        if v_isSharedCheck_2972_ == 0 {
                            v___x_2967_ = v___x_2936_;
                            v_isShared_2968_ = v_isSharedCheck_2972_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2965_);
                            leanh::lean_dec(v___x_2936_);
                            v___x_2967_ = leanh::lean_box(0);
                            v_isShared_2968_ = v_isSharedCheck_2972_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_2973_ = leanh::lean_ctor_get(v___x_2934_, 0);
                    v_isSharedCheck_2980_ = (!leanh::lean_is_exclusive(v___x_2934_)) as u8;
                    if v_isSharedCheck_2980_ == 0 {
                        v___x_2975_ = v___x_2934_;
                        v_isShared_2976_ = v_isSharedCheck_2980_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2973_);
                        leanh::lean_dec(v___x_2934_);
                        v___x_2975_ = leanh::lean_box(0);
                        v_isShared_2976_ = v_isSharedCheck_2980_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2951_, 0, v_a_2935_);
                leanh::lean_ctor_set(v___x_2951_, 1, v_a_2937_);
                if v_isShared_2950_ == 0 {
                    leanh::lean_ctor_set(v___x_2949_, 0, v___x_2951_);
                    v___x_2953_ = v___x_2949_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
                    v___x_2953_ = v_reuseFailAlloc_2954_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2953_;
            }
            3 => {
                if v_isShared_2960_ == 0 {
                    v___x_2962_ = v___x_2959_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2962_;
            }
            5 => {
                if v_isShared_2968_ == 0 {
                    v___x_2970_ = v___x_2967_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2971_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
                    v___x_2970_ = v_reuseFailAlloc_2971_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2970_;
            }
            7 => {
                if v_isShared_2976_ == 0 {
                    v___x_2978_ = v___x_2975_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2979_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
                    v___x_2978_ = v_reuseFailAlloc_2979_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2____boxed(
    mut v_a_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
    return v_res_2982_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2983_: *mut leanh::LeanObject,
    mut v_msg_2984_: *mut leanh::LeanObject,
    mut v___y_2985_: *mut leanh::LeanObject,
    mut v___y_2986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2988_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___redArg(v_msg_2984_, v___y_2985_, v___y_2986_);
    return v___x_2988_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2989_: *mut leanh::LeanObject,
    mut v_msg_2990_: *mut leanh::LeanObject,
    mut v___y_2991_: *mut leanh::LeanObject,
    mut v___y_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2994_ = l_Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0(v_00_u03b1_2989_, v_msg_2990_, v___y_2991_, v___y_2992_);
    leanh::lean_dec(v___y_2992_);
    leanh::lean_dec_ref(v___y_2991_);
    return v_res_2994_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(
    mut v_00_u03b1_2995_: *mut leanh::LeanObject,
    mut v_name_2996_: *mut leanh::LeanObject,
    mut v_kind_2997_: u8,
    mut v___y_2998_: *mut leanh::LeanObject,
    mut v___y_2999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3001_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg(v_name_2996_, v_kind_2997_, v___y_2998_, v___y_2999_);
    return v___x_3001_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___boxed(
    mut v_00_u03b1_3002_: *mut leanh::LeanObject,
    mut v_name_3003_: *mut leanh::LeanObject,
    mut v_kind_3004_: *mut leanh::LeanObject,
    mut v___y_3005_: *mut leanh::LeanObject,
    mut v___y_3006_: *mut leanh::LeanObject,
    mut v___y_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_3008_: u8 = 0;
    let mut v_res_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3008_ = (leanh::lean_unbox(v_kind_3004_) as u8);
    v_res_3009_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2(v_00_u03b1_3002_, v_name_3003_, v_kind_boxed_3008_, v___y_3005_, v___y_3006_);
    leanh::lean_dec(v___y_3006_);
    leanh::lean_dec_ref(v___y_3005_);
    return v_res_3009_;
}
pub unsafe fn l_Lean_getSuggestions___redArg___lam__1(
    mut v_incorrectName_3032_: *mut leanh::LeanObject,
    mut v___f_3033_: *mut leanh::LeanObject,
    mut v___f_3034_: *mut leanh::LeanObject,
    mut v_x1_3035_: *mut leanh::LeanObject,
    mut v_x2_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    v___x_3037_ = leanh::lean_unsigned_to_nat(0);
    v___x_3038_ = lean_array_get_size(v_x2_3036_);
    v___x_3039_ = lean_nat_dec_lt(v___x_3037_, v___x_3038_);
    if v___x_3039_ == 0 {
        leanh::lean_dec_ref(v___f_3034_);
        leanh::lean_dec_ref(v___f_3033_);
        leanh::lean_dec(v_incorrectName_3032_);
        return v_x1_3035_;
    } else {
        let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3042_: u8 = 0;
        v___x_3040_ = leanh::lean_unsigned_to_nat(1);
        v___x_3041_ = lean_nat_sub(v___x_3038_, v___x_3040_);
        v___x_3042_ = lean_nat_dec_le(v___x_3037_, v___x_3041_);
        if v___x_3042_ == 0 {
            leanh::lean_dec(v___x_3041_);
            leanh::lean_dec_ref(v___f_3034_);
            leanh::lean_dec_ref(v___f_3033_);
            leanh::lean_dec(v_incorrectName_3032_);
            return v_x1_3035_;
        } else {
            let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3043_ = l_Lean_getSuggestions___redArg___lam__1___closed__0;
            v___x_3044_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3044_, 0, v_incorrectName_3032_);
            leanh::lean_ctor_set(v___x_3044_, 1, v___x_3043_);
            v___x_3045_ = l_Lean_getSuggestions___redArg___lam__1___closed__1;
            v___x_3046_ = l_Array_binSearchAux___redArg(
                v___f_3033_,
                v___x_3045_,
                v_x2_3036_,
                v___x_3044_,
                v___x_3037_,
                v___x_3041_,
            );
            if leanh::lean_obj_tag(v___x_3046_) == 0 {
                leanh::lean_dec_ref(v___f_3034_);
                return v_x1_3035_;
            } else {
                let mut v_val_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_snd_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3051_: u8 = 0;
                v_val_3047_ = leanh::lean_ctor_get(v___x_3046_, 0);
                leanh::lean_inc(v_val_3047_);
                leanh::lean_dec_ref_known(v___x_3046_, 1);
                v_snd_3048_ = leanh::lean_ctor_get(v_val_3047_, 1);
                leanh::lean_inc(v_snd_3048_);
                leanh::lean_dec(v_val_3047_);
                v___x_3049_ = lean_array_get_size(v_snd_3048_);
                v___x_3050_ = l_Lean_getSuggestions___redArg___lam__1___closed__11;
                v___x_3051_ = lean_nat_dec_lt(v___x_3037_, v___x_3049_);
                if v___x_3051_ == 0 {
                    leanh::lean_dec(v_snd_3048_);
                    leanh::lean_dec_ref(v___f_3034_);
                    return v_x1_3035_;
                } else {
                    let mut v___x_3052_: u8 = 0;
                    v___x_3052_ = lean_nat_dec_le(v___x_3049_, v___x_3049_);
                    if v___x_3052_ == 0 {
                        if v___x_3051_ == 0 {
                            leanh::lean_dec(v_snd_3048_);
                            leanh::lean_dec_ref(v___f_3034_);
                            return v_x1_3035_;
                        } else {
                            let mut v___x_3053_: usize = 0;
                            let mut v___x_3054_: usize = 0;
                            let mut v___x_3055_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_3053_ = 0usize;
                            v___x_3054_ = lean_usize_of_nat(v___x_3049_);
                            v___x_3055_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_3050_,
                                    v___f_3034_,
                                    v_snd_3048_,
                                    v___x_3053_,
                                    v___x_3054_,
                                    v_x1_3035_,
                                );
                            return v___x_3055_;
                        }
                    } else {
                        let mut v___x_3056_: usize = 0;
                        let mut v___x_3057_: usize = 0;
                        let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_3056_ = 0usize;
                        v___x_3057_ = lean_usize_of_nat(v___x_3049_);
                        v___x_3058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3050_,
                            v___f_3034_,
                            v_snd_3048_,
                            v___x_3056_,
                            v___x_3057_,
                            v_x1_3035_,
                        );
                        return v___x_3058_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_getSuggestions___redArg___lam__1___boxed(
    mut v_incorrectName_3059_: *mut leanh::LeanObject,
    mut v___f_3060_: *mut leanh::LeanObject,
    mut v___f_3061_: *mut leanh::LeanObject,
    mut v_x1_3062_: *mut leanh::LeanObject,
    mut v_x2_3063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3064_ = l_Lean_getSuggestions___redArg___lam__1(
        v_incorrectName_3059_,
        v___f_3060_,
        v___f_3061_,
        v_x1_3062_,
        v_x2_3063_,
    );
    leanh::lean_dec_ref(v_x2_3063_);
    return v_res_3064_;
}
pub unsafe fn l_Lean_getSuggestions___redArg___lam__0(
    mut v___x_3065_: *mut leanh::LeanObject,
    mut v_toPure_3066_: *mut leanh::LeanObject,
    mut v___f_3067_: *mut leanh::LeanObject,
    mut v_incorrectName_3068_: *mut leanh::LeanObject,
    mut v_env_3069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: usize = 0;
    let mut v___x_3088_: usize = 0;
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: usize = 0;
    let mut v___x_3092_: usize = 0;
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3070_ =
                    l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
                v_snd_3071_ = leanh::lean_ctor_get(v___x_3070_, 1);
                v_toEnvExtension_3072_ = leanh::lean_ctor_get(v_snd_3071_, 0);
                v_asyncMode_3073_ = leanh::lean_ctor_get(v_toEnvExtension_3072_, 2);
                v___x_3074_ = leanh::lean_box(0);
                v___x_3075_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_3065_,
                        v_toEnvExtension_3072_,
                        v_env_3069_,
                        v_asyncMode_3073_,
                        v___x_3074_,
                    );
                v_importedEntries_3076_ = leanh::lean_ctor_get(v___x_3075_, 0);
                leanh::lean_inc_ref(v_importedEntries_3076_);
                v_state_3077_ = leanh::lean_ctor_get(v___x_3075_, 1);
                leanh::lean_inc(v_state_3077_);
                leanh::lean_dec(v___x_3075_);
                v___x_3095_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_3077_, v_incorrectName_3068_);
                leanh::lean_dec(v_state_3077_);
                if leanh::lean_obj_tag(v___x_3095_) == 0 {
                    v___x_3096_ = l_Lean_NameSet_empty;
                    v___y_3079_ = v___x_3096_;
                    state = 1;
                    continue;
                } else {
                    v_val_3097_ = leanh::lean_ctor_get(v___x_3095_, 0);
                    leanh::lean_inc(v_val_3097_);
                    leanh::lean_dec_ref_known(v___x_3095_, 1);
                    v___y_3079_ = v_val_3097_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3080_ = leanh::lean_unsigned_to_nat(0);
                v___x_3081_ = lean_array_get_size(v_importedEntries_3076_);
                v___x_3082_ = l_Lean_getSuggestions___redArg___lam__1___closed__11;
                v___x_3083_ = lean_nat_dec_lt(v___x_3080_, v___x_3081_);
                if v___x_3083_ == 0 {
                    leanh::lean_dec_ref(v_importedEntries_3076_);
                    leanh::lean_dec_ref(v___f_3067_);
                    v___x_3084_ = leanh::lean_apply_2(
                        v_toPure_3066_,
                        leanh::lean_box(0),
                        v___y_3079_,
                    );
                    return v___x_3084_;
                } else {
                    v___x_3085_ = lean_nat_dec_le(v___x_3081_, v___x_3081_);
                    if v___x_3085_ == 0 {
                        if v___x_3083_ == 0 {
                            leanh::lean_dec_ref(v_importedEntries_3076_);
                            leanh::lean_dec_ref(v___f_3067_);
                            v___x_3086_ = leanh::lean_apply_2(
                                v_toPure_3066_,
                                leanh::lean_box(0),
                                v___y_3079_,
                            );
                            return v___x_3086_;
                        } else {
                            v___x_3087_ = 0usize;
                            v___x_3088_ = lean_usize_of_nat(v___x_3081_);
                            v___x_3089_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_3082_,
                                    v___f_3067_,
                                    v_importedEntries_3076_,
                                    v___x_3087_,
                                    v___x_3088_,
                                    v___y_3079_,
                                );
                            v___x_3090_ = leanh::lean_apply_2(
                                v_toPure_3066_,
                                leanh::lean_box(0),
                                v___x_3089_,
                            );
                            return v___x_3090_;
                        }
                    } else {
                        v___x_3091_ = 0usize;
                        v___x_3092_ = lean_usize_of_nat(v___x_3081_);
                        v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3082_,
                            v___f_3067_,
                            v_importedEntries_3076_,
                            v___x_3091_,
                            v___x_3092_,
                            v___y_3079_,
                        );
                        v___x_3094_ = leanh::lean_apply_2(
                            v_toPure_3066_,
                            leanh::lean_box(0),
                            v___x_3093_,
                        );
                        return v___x_3094_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getSuggestions___redArg___lam__0___boxed(
    mut v___x_3098_: *mut leanh::LeanObject,
    mut v_toPure_3099_: *mut leanh::LeanObject,
    mut v___f_3100_: *mut leanh::LeanObject,
    mut v_incorrectName_3101_: *mut leanh::LeanObject,
    mut v_env_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3103_ = l_Lean_getSuggestions___redArg___lam__0(
        v___x_3098_,
        v_toPure_3099_,
        v___f_3100_,
        v_incorrectName_3101_,
        v_env_3102_,
    );
    leanh::lean_dec(v_incorrectName_3101_);
    leanh::lean_dec_ref(v___x_3098_);
    return v_res_3103_;
}
pub unsafe fn _init_l_Lean_getSuggestions___redArg___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = leanh::lean_box(1);
    v___x_3107_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3106_);
    return v___x_3107_;
}
pub unsafe fn l_Lean_getSuggestions___redArg(
    mut v_inst_3108_: *mut leanh::LeanObject,
    mut v_inst_3109_: *mut leanh::LeanObject,
    mut v_incorrectName_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3111_ = leanh::lean_ctor_get(v_inst_3108_, 0);
    leanh::lean_inc_ref(v_toApplicative_3111_);
    v_toBind_3112_ = leanh::lean_ctor_get(v_inst_3108_, 1);
    leanh::lean_inc(v_toBind_3112_);
    leanh::lean_dec_ref(v_inst_3108_);
    v_getEnv_3113_ = leanh::lean_ctor_get(v_inst_3109_, 0);
    leanh::lean_inc(v_getEnv_3113_);
    leanh::lean_dec_ref(v_inst_3109_);
    v_toPure_3114_ = leanh::lean_ctor_get(v_toApplicative_3111_, 1);
    leanh::lean_inc(v_toPure_3114_);
    leanh::lean_dec_ref(v_toApplicative_3111_);
    v___f_3115_ = l_Lean_getSuggestions___redArg___closed__0;
    v___f_3116_ = l_Lean_getSuggestions___redArg___closed__1;
    leanh::lean_inc(v_incorrectName_3110_);
    v___f_3117_ = leanh::lean_alloc_closure(
        l_Lean_getSuggestions___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_3117_, 0, v_incorrectName_3110_);
    leanh::lean_closure_set(v___f_3117_, 1, v___f_3115_);
    leanh::lean_closure_set(v___f_3117_, 2, v___f_3116_);
    v___x_3118_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getSuggestions___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getSuggestions___redArg___closed__2_once),
        _init_l_Lean_getSuggestions___redArg___closed__2,
    );
    v___f_3119_ = leanh::lean_alloc_closure(
        l_Lean_getSuggestions___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_3119_, 0, v___x_3118_);
    leanh::lean_closure_set(v___f_3119_, 1, v_toPure_3114_);
    leanh::lean_closure_set(v___f_3119_, 2, v___f_3117_);
    leanh::lean_closure_set(v___f_3119_, 3, v_incorrectName_3110_);
    v___x_3120_ = leanh::lean_apply_4(
        v_toBind_3112_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_3113_,
        v___f_3119_,
    );
    return v___x_3120_;
}
pub unsafe fn l_Lean_getSuggestions(
    mut v_m_3121_: *mut leanh::LeanObject,
    mut v_inst_3122_: *mut leanh::LeanObject,
    mut v_inst_3123_: *mut leanh::LeanObject,
    mut v_incorrectName_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3125_ = l_Lean_getSuggestions___redArg(v_inst_3122_, v_inst_3123_, v_incorrectName_3124_);
    return v___x_3125_;
}
pub unsafe fn l_Lean_getStoredSuggestions___redArg___lam__1(
    mut v_trueName_3126_: *mut leanh::LeanObject,
    mut v___f_3127_: *mut leanh::LeanObject,
    mut v___f_3128_: *mut leanh::LeanObject,
    mut v_x1_3129_: *mut leanh::LeanObject,
    mut v_x2_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: u8 = 0;
    v___x_3131_ = leanh::lean_unsigned_to_nat(0);
    v___x_3132_ = lean_array_get_size(v_x2_3130_);
    v___x_3133_ = lean_nat_dec_lt(v___x_3131_, v___x_3132_);
    if v___x_3133_ == 0 {
        leanh::lean_dec_ref(v___f_3128_);
        leanh::lean_dec_ref(v___f_3127_);
        leanh::lean_dec(v_trueName_3126_);
        return v_x1_3129_;
    } else {
        let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3136_: u8 = 0;
        v___x_3134_ = leanh::lean_unsigned_to_nat(1);
        v___x_3135_ = lean_nat_sub(v___x_3132_, v___x_3134_);
        v___x_3136_ = lean_nat_dec_le(v___x_3131_, v___x_3135_);
        if v___x_3136_ == 0 {
            leanh::lean_dec(v___x_3135_);
            leanh::lean_dec_ref(v___f_3128_);
            leanh::lean_dec_ref(v___f_3127_);
            leanh::lean_dec(v_trueName_3126_);
            return v_x1_3129_;
        } else {
            let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3137_ = l_Lean_getSuggestions___redArg___lam__1___closed__0;
            v___x_3138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3138_, 0, v_trueName_3126_);
            leanh::lean_ctor_set(v___x_3138_, 1, v___x_3137_);
            v___x_3139_ = l_Lean_getSuggestions___redArg___lam__1___closed__1;
            v___x_3140_ = l_Array_binSearchAux___redArg(
                v___f_3127_,
                v___x_3139_,
                v_x2_3130_,
                v___x_3138_,
                v___x_3131_,
                v___x_3135_,
            );
            if leanh::lean_obj_tag(v___x_3140_) == 0 {
                leanh::lean_dec_ref(v___f_3128_);
                return v_x1_3129_;
            } else {
                let mut v_val_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_snd_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3145_: u8 = 0;
                v_val_3141_ = leanh::lean_ctor_get(v___x_3140_, 0);
                leanh::lean_inc(v_val_3141_);
                leanh::lean_dec_ref_known(v___x_3140_, 1);
                v_snd_3142_ = leanh::lean_ctor_get(v_val_3141_, 1);
                leanh::lean_inc(v_snd_3142_);
                leanh::lean_dec(v_val_3141_);
                v___x_3143_ = lean_array_get_size(v_snd_3142_);
                v___x_3144_ = l_Lean_getSuggestions___redArg___lam__1___closed__11;
                v___x_3145_ = lean_nat_dec_lt(v___x_3131_, v___x_3143_);
                if v___x_3145_ == 0 {
                    leanh::lean_dec(v_snd_3142_);
                    leanh::lean_dec_ref(v___f_3128_);
                    return v_x1_3129_;
                } else {
                    let mut v___x_3146_: u8 = 0;
                    v___x_3146_ = lean_nat_dec_le(v___x_3143_, v___x_3143_);
                    if v___x_3146_ == 0 {
                        if v___x_3145_ == 0 {
                            leanh::lean_dec(v_snd_3142_);
                            leanh::lean_dec_ref(v___f_3128_);
                            return v_x1_3129_;
                        } else {
                            let mut v___x_3147_: usize = 0;
                            let mut v___x_3148_: usize = 0;
                            let mut v___x_3149_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_3147_ = 0usize;
                            v___x_3148_ = lean_usize_of_nat(v___x_3143_);
                            v___x_3149_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_3144_,
                                    v___f_3128_,
                                    v_snd_3142_,
                                    v___x_3147_,
                                    v___x_3148_,
                                    v_x1_3129_,
                                );
                            return v___x_3149_;
                        }
                    } else {
                        let mut v___x_3150_: usize = 0;
                        let mut v___x_3151_: usize = 0;
                        let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_3150_ = 0usize;
                        v___x_3151_ = lean_usize_of_nat(v___x_3143_);
                        v___x_3152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3144_,
                            v___f_3128_,
                            v_snd_3142_,
                            v___x_3150_,
                            v___x_3151_,
                            v_x1_3129_,
                        );
                        return v___x_3152_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_getStoredSuggestions___redArg___lam__1___boxed(
    mut v_trueName_3153_: *mut leanh::LeanObject,
    mut v___f_3154_: *mut leanh::LeanObject,
    mut v___f_3155_: *mut leanh::LeanObject,
    mut v_x1_3156_: *mut leanh::LeanObject,
    mut v_x2_3157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3158_ = l_Lean_getStoredSuggestions___redArg___lam__1(
        v_trueName_3153_,
        v___f_3154_,
        v___f_3155_,
        v_x1_3156_,
        v_x2_3157_,
    );
    leanh::lean_dec_ref(v_x2_3157_);
    return v_res_3158_;
}
pub unsafe fn l_Lean_getStoredSuggestions___redArg___lam__0(
    mut v___x_3159_: *mut leanh::LeanObject,
    mut v_toPure_3160_: *mut leanh::LeanObject,
    mut v___f_3161_: *mut leanh::LeanObject,
    mut v_trueName_3162_: *mut leanh::LeanObject,
    mut v_env_3163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: u8 = 0;
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: usize = 0;
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: usize = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3164_ =
                    l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
                v_fst_3165_ = leanh::lean_ctor_get(v___x_3164_, 0);
                v_toEnvExtension_3166_ = leanh::lean_ctor_get(v_fst_3165_, 0);
                v_asyncMode_3167_ = leanh::lean_ctor_get(v_toEnvExtension_3166_, 2);
                v___x_3168_ = leanh::lean_box(0);
                v___x_3169_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_3159_,
                        v_toEnvExtension_3166_,
                        v_env_3163_,
                        v_asyncMode_3167_,
                        v___x_3168_,
                    );
                v_importedEntries_3170_ = leanh::lean_ctor_get(v___x_3169_, 0);
                leanh::lean_inc_ref(v_importedEntries_3170_);
                v_state_3171_ = leanh::lean_ctor_get(v___x_3169_, 1);
                leanh::lean_inc(v_state_3171_);
                leanh::lean_dec(v___x_3169_);
                v___x_3189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_3171_, v_trueName_3162_);
                leanh::lean_dec(v_state_3171_);
                if leanh::lean_obj_tag(v___x_3189_) == 0 {
                    v___x_3190_ = l_Lean_NameSet_empty;
                    v___y_3173_ = v___x_3190_;
                    state = 1;
                    continue;
                } else {
                    v_val_3191_ = leanh::lean_ctor_get(v___x_3189_, 0);
                    leanh::lean_inc(v_val_3191_);
                    leanh::lean_dec_ref_known(v___x_3189_, 1);
                    v___y_3173_ = v_val_3191_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3174_ = leanh::lean_unsigned_to_nat(0);
                v___x_3175_ = lean_array_get_size(v_importedEntries_3170_);
                v___x_3176_ = l_Lean_getSuggestions___redArg___lam__1___closed__11;
                v___x_3177_ = lean_nat_dec_lt(v___x_3174_, v___x_3175_);
                if v___x_3177_ == 0 {
                    leanh::lean_dec_ref(v_importedEntries_3170_);
                    leanh::lean_dec_ref(v___f_3161_);
                    v___x_3178_ = leanh::lean_apply_2(
                        v_toPure_3160_,
                        leanh::lean_box(0),
                        v___y_3173_,
                    );
                    return v___x_3178_;
                } else {
                    v___x_3179_ = lean_nat_dec_le(v___x_3175_, v___x_3175_);
                    if v___x_3179_ == 0 {
                        if v___x_3177_ == 0 {
                            leanh::lean_dec_ref(v_importedEntries_3170_);
                            leanh::lean_dec_ref(v___f_3161_);
                            v___x_3180_ = leanh::lean_apply_2(
                                v_toPure_3160_,
                                leanh::lean_box(0),
                                v___y_3173_,
                            );
                            return v___x_3180_;
                        } else {
                            v___x_3181_ = 0usize;
                            v___x_3182_ = lean_usize_of_nat(v___x_3175_);
                            v___x_3183_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_3176_,
                                    v___f_3161_,
                                    v_importedEntries_3170_,
                                    v___x_3181_,
                                    v___x_3182_,
                                    v___y_3173_,
                                );
                            v___x_3184_ = leanh::lean_apply_2(
                                v_toPure_3160_,
                                leanh::lean_box(0),
                                v___x_3183_,
                            );
                            return v___x_3184_;
                        }
                    } else {
                        v___x_3185_ = 0usize;
                        v___x_3186_ = lean_usize_of_nat(v___x_3175_);
                        v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3176_,
                            v___f_3161_,
                            v_importedEntries_3170_,
                            v___x_3185_,
                            v___x_3186_,
                            v___y_3173_,
                        );
                        v___x_3188_ = leanh::lean_apply_2(
                            v_toPure_3160_,
                            leanh::lean_box(0),
                            v___x_3187_,
                        );
                        return v___x_3188_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getStoredSuggestions___redArg___lam__0___boxed(
    mut v___x_3192_: *mut leanh::LeanObject,
    mut v_toPure_3193_: *mut leanh::LeanObject,
    mut v___f_3194_: *mut leanh::LeanObject,
    mut v_trueName_3195_: *mut leanh::LeanObject,
    mut v_env_3196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3197_ = l_Lean_getStoredSuggestions___redArg___lam__0(
        v___x_3192_,
        v_toPure_3193_,
        v___f_3194_,
        v_trueName_3195_,
        v_env_3196_,
    );
    leanh::lean_dec(v_trueName_3195_);
    leanh::lean_dec_ref(v___x_3192_);
    return v_res_3197_;
}
pub unsafe fn l_Lean_getStoredSuggestions___redArg(
    mut v_inst_3198_: *mut leanh::LeanObject,
    mut v_inst_3199_: *mut leanh::LeanObject,
    mut v_trueName_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3201_ = leanh::lean_ctor_get(v_inst_3198_, 0);
    leanh::lean_inc_ref(v_toApplicative_3201_);
    v_toBind_3202_ = leanh::lean_ctor_get(v_inst_3198_, 1);
    leanh::lean_inc(v_toBind_3202_);
    leanh::lean_dec_ref(v_inst_3198_);
    v_getEnv_3203_ = leanh::lean_ctor_get(v_inst_3199_, 0);
    leanh::lean_inc(v_getEnv_3203_);
    leanh::lean_dec_ref(v_inst_3199_);
    v_toPure_3204_ = leanh::lean_ctor_get(v_toApplicative_3201_, 1);
    leanh::lean_inc(v_toPure_3204_);
    leanh::lean_dec_ref(v_toApplicative_3201_);
    v___f_3205_ = l_Lean_getSuggestions___redArg___closed__0;
    v___f_3206_ = l_Lean_getSuggestions___redArg___closed__1;
    leanh::lean_inc(v_trueName_3200_);
    v___f_3207_ = leanh::lean_alloc_closure(
        l_Lean_getStoredSuggestions___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_3207_, 0, v_trueName_3200_);
    leanh::lean_closure_set(v___f_3207_, 1, v___f_3205_);
    leanh::lean_closure_set(v___f_3207_, 2, v___f_3206_);
    v___x_3208_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getSuggestions___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getSuggestions___redArg___closed__2_once),
        _init_l_Lean_getSuggestions___redArg___closed__2,
    );
    v___f_3209_ = leanh::lean_alloc_closure(
        l_Lean_getStoredSuggestions___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_3209_, 0, v___x_3208_);
    leanh::lean_closure_set(v___f_3209_, 1, v_toPure_3204_);
    leanh::lean_closure_set(v___f_3209_, 2, v___f_3207_);
    leanh::lean_closure_set(v___f_3209_, 3, v_trueName_3200_);
    v___x_3210_ = leanh::lean_apply_4(
        v_toBind_3202_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_3203_,
        v___f_3209_,
    );
    return v___x_3210_;
}
pub unsafe fn l_Lean_getStoredSuggestions(
    mut v_m_3211_: *mut leanh::LeanObject,
    mut v_inst_3212_: *mut leanh::LeanObject,
    mut v_inst_3213_: *mut leanh::LeanObject,
    mut v_trueName_3214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3215_ =
        l_Lean_getStoredSuggestions___redArg(v_inst_3212_, v_inst_3213_, v_trueName_3214_);
    return v___x_3215_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(
    mut v_x_3217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___closed__0;
    v___x_3219_ = lean_string_append(v___x_3218_, v_x_3217_);
    return v___x_3219_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0___boxed(
    mut v_x_3220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___lam__0(v_x_3220_);
    leanh::lean_dec_ref(v_x_3220_);
    return v_res_3221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(
    mut v___x_3225_: *mut leanh::LeanObject,
    mut v___x_3226_: *mut leanh::LeanObject,
    mut v___x_3227_: *mut leanh::LeanObject,
    mut v___x_3228_: *mut leanh::LeanObject,
    mut v_sz_3229_: usize,
    mut v_i_3230_: usize,
    mut v_bs_3231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3232_: u8 = 0;
    let mut v_v_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: u8 = 0;
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3232_ = lean_usize_dec_lt(v_i_3230_, v_sz_3229_);
                if v___x_3232_ == 0 {
                    leanh::lean_dec(v___x_3228_);
                    leanh::lean_dec(v___x_3227_);
                    leanh::lean_dec_ref(v___x_3226_);
                    return v_bs_3231_;
                } else {
                    v_v_3233_ = lean_array_uget(v_bs_3231_, v_i_3230_);
                    v___x_3234_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3235_ = lean_array_uset(v_bs_3231_, v_i_3230_, v___x_3234_);
                    if leanh::lean_obj_tag(v___x_3225_) == 0 {
                        leanh::lean_inc(v_v_3233_);
                        v___y_3237_ = v_v_3233_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3255_ = leanh::lean_ctor_get(v___x_3225_, 0);
                        v___x_3256_ = leanh::lean_box(0);
                        leanh::lean_inc(v_v_3233_);
                        v___x_3257_ =
                            l_Lean_Name_replacePrefix(v_v_3233_, v_val_3255_, v___x_3256_);
                        v___x_3258_ = l_Lean_Options_empty;
                        leanh::lean_inc(v___x_3257_);
                        leanh::lean_inc(v___x_3228_);
                        leanh::lean_inc(v___x_3227_);
                        leanh::lean_inc_ref(v___x_3226_);
                        v___x_3259_ = l_Lean_ResolveName_resolveGlobalName(
                            v___x_3226_,
                            v___x_3258_,
                            v___x_3227_,
                            v___x_3228_,
                            v___x_3257_,
                        );
                        v___x_3260_ = l_List_lengthTR___redArg(v___x_3259_);
                        leanh::lean_dec(v___x_3259_);
                        v___x_3261_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3262_ = lean_nat_dec_eq(v___x_3260_, v___x_3261_);
                        leanh::lean_dec(v___x_3260_);
                        if v___x_3262_ == 0 {
                            leanh::lean_dec(v___x_3257_);
                            leanh::lean_inc(v_v_3233_);
                            v___y_3237_ = v_v_3233_;
                            state = 1;
                            continue;
                        } else {
                            v___y_3237_ = v___x_3257_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3238_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___y_3237_,
                    v___x_3232_,
                );
                v___x_3239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3239_, 0, v___x_3238_);
                v___x_3240_ = leanh::lean_box(0);
                v___x_3241_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
                v___x_3242_ = 0;
                v___x_3243_ = l_Lean_MessageData_ofConstName(v_v_3233_, v___x_3242_);
                v___x_3244_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3244_, 0, v___x_3241_);
                leanh::lean_ctor_set(v___x_3244_, 1, v___x_3243_);
                v___x_3245_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3245_, 0, v___x_3244_);
                leanh::lean_ctor_set(v___x_3245_, 1, v___x_3241_);
                v___x_3246_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3246_, 0, v___x_3245_);
                v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___closed__1;
                v___x_3248_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_3248_, 0, v___x_3239_);
                leanh::lean_ctor_set(v___x_3248_, 1, v___x_3240_);
                leanh::lean_ctor_set(v___x_3248_, 2, v___x_3240_);
                leanh::lean_ctor_set(v___x_3248_, 3, v___x_3240_);
                leanh::lean_ctor_set(v___x_3248_, 4, v___x_3246_);
                leanh::lean_ctor_set(v___x_3248_, 5, v___x_3247_);
                v___x_3249_ = 0;
                v___x_3250_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_3250_, 0, v___x_3248_);
                leanh::lean_ctor_set(v___x_3250_, 1, v___x_3240_);
                leanh::lean_ctor_set(v___x_3250_, 2, v___x_3240_);
                leanh::lean_ctor_set_uint8(
                    v___x_3250_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3249_,
                );
                v___x_3251_ = 1usize;
                v___x_3252_ = lean_usize_add(v_i_3230_, v___x_3251_);
                v___x_3253_ = lean_array_uset(v_bs_x27_3235_, v_i_3230_, v___x_3250_);
                v_i_3230_ = v___x_3252_;
                v_bs_3231_ = v___x_3253_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2___boxed(
    mut v___x_3263_: *mut leanh::LeanObject,
    mut v___x_3264_: *mut leanh::LeanObject,
    mut v___x_3265_: *mut leanh::LeanObject,
    mut v___x_3266_: *mut leanh::LeanObject,
    mut v_sz_3267_: *mut leanh::LeanObject,
    mut v_i_3268_: *mut leanh::LeanObject,
    mut v_bs_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3270_: usize = 0;
    let mut v_i_boxed_3271_: usize = 0;
    let mut v_res_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3270_ = leanh::lean_unbox_usize(v_sz_3267_);
    leanh::lean_dec(v_sz_3267_);
    v_i_boxed_3271_ = leanh::lean_unbox_usize(v_i_3268_);
    leanh::lean_dec(v_i_3268_);
    v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___x_3263_, v___x_3264_, v___x_3265_, v___x_3266_, v_sz_boxed_3270_, v_i_boxed_3271_, v_bs_3269_);
    leanh::lean_dec(v___x_3263_);
    return v_res_3272_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(
    mut v_msgData_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
    mut v___y_3277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3279_ = lean_st_ref_get(v___y_3277_);
    v_env_3280_ = leanh::lean_ctor_get(v___x_3279_, 0);
    leanh::lean_inc_ref(v_env_3280_);
    leanh::lean_dec(v___x_3279_);
    v___x_3281_ = lean_st_ref_get(v___y_3275_);
    v_mctx_3282_ = leanh::lean_ctor_get(v___x_3281_, 0);
    leanh::lean_inc_ref(v_mctx_3282_);
    leanh::lean_dec(v___x_3281_);
    v_lctx_3283_ = leanh::lean_ctor_get(v___y_3274_, 2);
    v_options_3284_ = leanh::lean_ctor_get(v___y_3276_, 2);
    leanh::lean_inc_ref(v_options_3284_);
    leanh::lean_inc_ref(v_lctx_3283_);
    v___x_3285_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3285_, 0, v_env_3280_);
    leanh::lean_ctor_set(v___x_3285_, 1, v_mctx_3282_);
    leanh::lean_ctor_set(v___x_3285_, 2, v_lctx_3283_);
    leanh::lean_ctor_set(v___x_3285_, 3, v_options_3284_);
    v___x_3286_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3286_, 0, v___x_3285_);
    leanh::lean_ctor_set(v___x_3286_, 1, v_msgData_3273_);
    v___x_3287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3287_, 0, v___x_3286_);
    return v___x_3287_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8___boxed(
    mut v_msgData_3288_: *mut leanh::LeanObject,
    mut v___y_3289_: *mut leanh::LeanObject,
    mut v___y_3290_: *mut leanh::LeanObject,
    mut v___y_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
    mut v___y_3293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3294_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msgData_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
    leanh::lean_dec(v___y_3292_);
    leanh::lean_dec_ref(v___y_3291_);
    leanh::lean_dec(v___y_3290_);
    leanh::lean_dec_ref(v___y_3289_);
    return v_res_3294_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3295_ = leanh::lean_box(1);
    v___x_3296_ = l_Lean_MessageData_ofFormat(v___x_3295_);
    return v___x_3296_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3300_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__2;
    v___x_3301_ = l_Lean_MessageData_ofFormat(v___x_3300_);
    return v___x_3301_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(
    mut v_x_3302_: *mut leanh::LeanObject,
    mut v_x_3303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v_before_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_unused_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3303_) == 0 {
                    return v_x_3302_;
                } else {
                    v_head_3304_ = leanh::lean_ctor_get(v_x_3303_, 0);
                    v_tail_3305_ = leanh::lean_ctor_get(v_x_3303_, 1);
                    v_isSharedCheck_3327_ = (!leanh::lean_is_exclusive(v_x_3303_)) as u8;
                    if v_isSharedCheck_3327_ == 0 {
                        v___x_3307_ = v_x_3303_;
                        v_isShared_3308_ = v_isSharedCheck_3327_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3305_);
                        leanh::lean_inc(v_head_3304_);
                        leanh::lean_dec(v_x_3303_);
                        v___x_3307_ = leanh::lean_box(0);
                        v_isShared_3308_ = v_isSharedCheck_3327_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3309_ = leanh::lean_ctor_get(v_head_3304_, 0);
                v_isSharedCheck_3325_ = (!leanh::lean_is_exclusive(v_head_3304_)) as u8;
                if v_isSharedCheck_3325_ == 0 {
                    v_unused_3326_ = leanh::lean_ctor_get(v_head_3304_, 1);
                    leanh::lean_dec(v_unused_3326_);
                    v___x_3311_ = v_head_3304_;
                    v_isShared_3312_ = v_isSharedCheck_3325_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_3309_);
                    leanh::lean_dec(v_head_3304_);
                    v___x_3311_ = leanh::lean_box(0);
                    v_isShared_3312_ = v_isSharedCheck_3325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3313_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
                if v_isShared_3312_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3311_, 7);
                    leanh::lean_ctor_set(v___x_3311_, 1, v___x_3313_);
                    leanh::lean_ctor_set(v___x_3311_, 0, v_x_3302_);
                    v___x_3315_ = v___x_3311_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_x_3302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3313_);
                    v___x_3315_ = v_reuseFailAlloc_3324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3316_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__3);
                if v_isShared_3308_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3307_, 7);
                    leanh::lean_ctor_set(v___x_3307_, 1, v___x_3316_);
                    leanh::lean_ctor_set(v___x_3307_, 0, v___x_3315_);
                    v___x_3318_ = v___x_3307_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3323_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___x_3316_);
                    v___x_3318_ = v_reuseFailAlloc_3323_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3319_ = l_Lean_MessageData_ofSyntax(v_before_3309_);
                v___x_3320_ = l_Lean_indentD(v___x_3319_);
                v___x_3321_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3321_, 0, v___x_3318_);
                leanh::lean_ctor_set(v___x_3321_, 1, v___x_3320_);
                v_x_3302_ = v___x_3321_;
                v_x_3303_ = v_tail_3305_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(
    mut v_opts_3328_: *mut leanh::LeanObject,
    mut v_opt_3329_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3330_ = leanh::lean_ctor_get(v_opt_3329_, 0);
    v_defValue_3331_ = leanh::lean_ctor_get(v_opt_3329_, 1);
    v_map_3332_ = leanh::lean_ctor_get(v_opts_3328_, 0);
    v___x_3333_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3332_,
            v_name_3330_,
        );
    if leanh::lean_obj_tag(v___x_3333_) == 0 {
        let mut v___x_3334_: u8 = 0;
        v___x_3334_ = (leanh::lean_unbox(v_defValue_3331_) as u8);
        return v___x_3334_;
    } else {
        let mut v_val_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3335_ = leanh::lean_ctor_get(v___x_3333_, 0);
        leanh::lean_inc(v_val_3335_);
        leanh::lean_dec_ref_known(v___x_3333_, 1);
        if leanh::lean_obj_tag(v_val_3335_) == 1 {
            let mut v_v_3336_: u8 = 0;
            v_v_3336_ = leanh::lean_ctor_get_uint8(v_val_3335_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3335_, 0);
            return v_v_3336_;
        } else {
            let mut v___x_3337_: u8 = 0;
            leanh::lean_dec(v_val_3335_);
            v___x_3337_ = (leanh::lean_unbox(v_defValue_3331_) as u8);
            return v___x_3337_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10___boxed(
    mut v_opts_3338_: *mut leanh::LeanObject,
    mut v_opt_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3340_: u8 = 0;
    let mut v_r_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3340_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_opts_3338_, v_opt_3339_);
    leanh::lean_dec_ref(v_opt_3339_);
    leanh::lean_dec_ref(v_opts_3338_);
    v_r_3341_ = leanh::lean_box((v_res_3340_) as usize);
    return v_r_3341_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__1;
    v___x_3346_ = l_Lean_MessageData_ofFormat(v___x_3345_);
    return v___x_3346_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(
    mut v_msgData_3347_: *mut leanh::LeanObject,
    mut v_macroStack_3348_: *mut leanh::LeanObject,
    mut v___y_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3360_: u8 = 0;
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3372_: u8 = 0;
    let mut v_unused_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3351_ = leanh::lean_ctor_get(v___y_3349_, 2);
                v___x_3352_ = l_Lean_Elab_pp_macroStack;
                v___x_3353_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__10(v_options_3351_, v___x_3352_);
                if v___x_3353_ == 0 {
                    leanh::lean_dec(v_macroStack_3348_);
                    v___x_3354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3354_, 0, v_msgData_3347_);
                    return v___x_3354_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_3348_) == 0 {
                        v___x_3355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3355_, 0, v_msgData_3347_);
                        return v___x_3355_;
                    } else {
                        v_head_3356_ = leanh::lean_ctor_get(v_macroStack_3348_, 0);
                        leanh::lean_inc(v_head_3356_);
                        v_after_3357_ = leanh::lean_ctor_get(v_head_3356_, 1);
                        v_isSharedCheck_3372_ =
                            (!leanh::lean_is_exclusive(v_head_3356_)) as u8;
                        if v_isSharedCheck_3372_ == 0 {
                            v_unused_3373_ = leanh::lean_ctor_get(v_head_3356_, 0);
                            leanh::lean_dec(v_unused_3373_);
                            v___x_3359_ = v_head_3356_;
                            v_isShared_3360_ = v_isSharedCheck_3372_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_3357_);
                            leanh::lean_dec(v_head_3356_);
                            v___x_3359_ = leanh::lean_box(0);
                            v_isShared_3360_ = v_isSharedCheck_3372_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3361_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
                if v_isShared_3360_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3359_, 7);
                    leanh::lean_ctor_set(v___x_3359_, 1, v___x_3361_);
                    leanh::lean_ctor_set(v___x_3359_, 0, v_msgData_3347_);
                    v___x_3363_ = v___x_3359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3371_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_msgData_3347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3371_, 1, v___x_3361_);
                    v___x_3363_ = v_reuseFailAlloc_3371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3364_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___closed__2);
                v___x_3365_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3365_, 0, v___x_3363_);
                leanh::lean_ctor_set(v___x_3365_, 1, v___x_3364_);
                v___x_3366_ = l_Lean_MessageData_ofSyntax(v_after_3357_);
                v___x_3367_ = l_Lean_indentD(v___x_3366_);
                v_msgData_3368_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_3368_, 0, v___x_3365_);
                leanh::lean_ctor_set(v_msgData_3368_, 1, v___x_3367_);
                v___x_3369_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11(v_msgData_3368_, v_macroStack_3348_);
                v___x_3370_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3370_, 0, v___x_3369_);
                return v___x_3370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg___boxed(
    mut v_msgData_3374_: *mut leanh::LeanObject,
    mut v_macroStack_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_3374_, v_macroStack_3375_, v___y_3376_);
    leanh::lean_dec_ref(v___y_3376_);
    return v_res_3378_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(
    mut v_msg_3379_: *mut leanh::LeanObject,
    mut v___y_3380_: *mut leanh::LeanObject,
    mut v___y_3381_: *mut leanh::LeanObject,
    mut v___y_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3396_: u8 = 0;
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3387_ = leanh::lean_ctor_get(v___y_3384_, 5);
                v___x_3388_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__8(v_msg_3379_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
                v_a_3389_ = leanh::lean_ctor_get(v___x_3388_, 0);
                leanh::lean_inc(v_a_3389_);
                leanh::lean_dec_ref(v___x_3388_);
                v_macroStack_3390_ = leanh::lean_ctor_get(v___y_3380_, 1);
                v___x_3391_ = l_Lean_Elab_getBetterRef(v_ref_3387_, v_macroStack_3390_);
                leanh::lean_inc(v_macroStack_3390_);
                v___x_3392_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_a_3389_, v_macroStack_3390_, v___y_3384_);
                v_a_3393_ = leanh::lean_ctor_get(v___x_3392_, 0);
                v_isSharedCheck_3401_ = (!leanh::lean_is_exclusive(v___x_3392_)) as u8;
                if v_isSharedCheck_3401_ == 0 {
                    v___x_3395_ = v___x_3392_;
                    v_isShared_3396_ = v_isSharedCheck_3401_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3393_);
                    leanh::lean_dec(v___x_3392_);
                    v___x_3395_ = leanh::lean_box(0);
                    v_isShared_3396_ = v_isSharedCheck_3401_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3397_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3397_, 0, v___x_3391_);
                leanh::lean_ctor_set(v___x_3397_, 1, v_a_3393_);
                if v_isShared_3396_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3395_, 1);
                    leanh::lean_ctor_set(v___x_3395_, 0, v___x_3397_);
                    v___x_3399_ = v___x_3395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3400_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
                    v___x_3399_ = v_reuseFailAlloc_3400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_msg_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3410_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
    leanh::lean_dec(v___y_3408_);
    leanh::lean_dec_ref(v___y_3407_);
    leanh::lean_dec(v___y_3406_);
    leanh::lean_dec_ref(v___y_3405_);
    leanh::lean_dec(v___y_3404_);
    leanh::lean_dec_ref(v___y_3403_);
    return v_res_3410_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(
    mut v_ref_3411_: *mut leanh::LeanObject,
    mut v_msg_3412_: *mut leanh::LeanObject,
    mut v___y_3413_: *mut leanh::LeanObject,
    mut v___y_3414_: *mut leanh::LeanObject,
    mut v___y_3415_: *mut leanh::LeanObject,
    mut v___y_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3432_: u8 = 0;
    let mut v_cancelTk_x3f_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3434_: u8 = 0;
    let mut v_inheritedTraceOptions_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3420_ = leanh::lean_ctor_get(v___y_3417_, 0);
    v_fileMap_3421_ = leanh::lean_ctor_get(v___y_3417_, 1);
    v_options_3422_ = leanh::lean_ctor_get(v___y_3417_, 2);
    v_currRecDepth_3423_ = leanh::lean_ctor_get(v___y_3417_, 3);
    v_maxRecDepth_3424_ = leanh::lean_ctor_get(v___y_3417_, 4);
    v_ref_3425_ = leanh::lean_ctor_get(v___y_3417_, 5);
    v_currNamespace_3426_ = leanh::lean_ctor_get(v___y_3417_, 6);
    v_openDecls_3427_ = leanh::lean_ctor_get(v___y_3417_, 7);
    v_initHeartbeats_3428_ = leanh::lean_ctor_get(v___y_3417_, 8);
    v_maxHeartbeats_3429_ = leanh::lean_ctor_get(v___y_3417_, 9);
    v_quotContext_3430_ = leanh::lean_ctor_get(v___y_3417_, 10);
    v_currMacroScope_3431_ = leanh::lean_ctor_get(v___y_3417_, 11);
    v_diag_3432_ = leanh::lean_ctor_get_uint8(
        v___y_3417_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3433_ = leanh::lean_ctor_get(v___y_3417_, 12);
    v_suppressElabErrors_3434_ = leanh::lean_ctor_get_uint8(
        v___y_3417_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3435_ = leanh::lean_ctor_get(v___y_3417_, 13);
    v_ref_3436_ = l_Lean_replaceRef(v_ref_3411_, v_ref_3425_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3435_);
    leanh::lean_inc(v_cancelTk_x3f_3433_);
    leanh::lean_inc(v_currMacroScope_3431_);
    leanh::lean_inc(v_quotContext_3430_);
    leanh::lean_inc(v_maxHeartbeats_3429_);
    leanh::lean_inc(v_initHeartbeats_3428_);
    leanh::lean_inc(v_openDecls_3427_);
    leanh::lean_inc(v_currNamespace_3426_);
    leanh::lean_inc(v_maxRecDepth_3424_);
    leanh::lean_inc(v_currRecDepth_3423_);
    leanh::lean_inc_ref(v_options_3422_);
    leanh::lean_inc_ref(v_fileMap_3421_);
    leanh::lean_inc_ref(v_fileName_3420_);
    v___x_3437_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3437_, 0, v_fileName_3420_);
    leanh::lean_ctor_set(v___x_3437_, 1, v_fileMap_3421_);
    leanh::lean_ctor_set(v___x_3437_, 2, v_options_3422_);
    leanh::lean_ctor_set(v___x_3437_, 3, v_currRecDepth_3423_);
    leanh::lean_ctor_set(v___x_3437_, 4, v_maxRecDepth_3424_);
    leanh::lean_ctor_set(v___x_3437_, 5, v_ref_3436_);
    leanh::lean_ctor_set(v___x_3437_, 6, v_currNamespace_3426_);
    leanh::lean_ctor_set(v___x_3437_, 7, v_openDecls_3427_);
    leanh::lean_ctor_set(v___x_3437_, 8, v_initHeartbeats_3428_);
    leanh::lean_ctor_set(v___x_3437_, 9, v_maxHeartbeats_3429_);
    leanh::lean_ctor_set(v___x_3437_, 10, v_quotContext_3430_);
    leanh::lean_ctor_set(v___x_3437_, 11, v_currMacroScope_3431_);
    leanh::lean_ctor_set(v___x_3437_, 12, v_cancelTk_x3f_3433_);
    leanh::lean_ctor_set(v___x_3437_, 13, v_inheritedTraceOptions_3435_);
    leanh::lean_ctor_set_uint8(
        v___x_3437_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3432_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3437_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3434_,
    );
    v___x_3438_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___x_3437_, v___y_3418_);
    leanh::lean_dec_ref_known(v___x_3437_, 14);
    return v___x_3438_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg___boxed(
    mut v_ref_3439_: *mut leanh::LeanObject,
    mut v_msg_3440_: *mut leanh::LeanObject,
    mut v___y_3441_: *mut leanh::LeanObject,
    mut v___y_3442_: *mut leanh::LeanObject,
    mut v___y_3443_: *mut leanh::LeanObject,
    mut v___y_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
    mut v___y_3446_: *mut leanh::LeanObject,
    mut v___y_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_3439_, v_msg_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
    leanh::lean_dec(v___y_3446_);
    leanh::lean_dec_ref(v___y_3445_);
    leanh::lean_dec(v___y_3444_);
    leanh::lean_dec_ref(v___y_3443_);
    leanh::lean_dec(v___y_3442_);
    leanh::lean_dec_ref(v___y_3441_);
    leanh::lean_dec(v_ref_3439_);
    return v_res_3448_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__0;
    v___x_3451_ = l_Lean_stringToMessageData(v___x_3450_);
    return v___x_3451_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__2;
    v___x_3454_ = l_Lean_stringToMessageData(v___x_3453_);
    return v___x_3454_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__4;
    v___x_3457_ = l_Lean_stringToMessageData(v___x_3456_);
    return v___x_3457_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3459_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__6;
    v___x_3460_ = l_Lean_stringToMessageData(v___x_3459_);
    return v___x_3460_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3462_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__8;
    v___x_3463_ = l_Lean_stringToMessageData(v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__10;
    v___x_3466_ = l_Lean_stringToMessageData(v___x_3465_);
    return v___x_3466_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__12;
    v___x_3469_ = l_Lean_stringToMessageData(v___x_3468_);
    return v___x_3469_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(
    mut v_msg_3470_: *mut leanh::LeanObject,
    mut v_declHint_3471_: *mut leanh::LeanObject,
    mut v___y_3472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v_isExporting_3477_: u8 = 0;
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3474_ = lean_st_ref_get(v___y_3472_);
                v_env_3475_ = leanh::lean_ctor_get(v___x_3474_, 0);
                leanh::lean_inc_ref(v_env_3475_);
                leanh::lean_dec(v___x_3474_);
                v___x_3476_ = l_Lean_Name_isAnonymous(v_declHint_3471_);
                if v___x_3476_ == 0 {
                    v_isExporting_3477_ = leanh::lean_ctor_get_uint8(
                        v_env_3475_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3477_ == 0 {
                        leanh::lean_dec_ref(v_env_3475_);
                        leanh::lean_dec(v_declHint_3471_);
                        v___x_3478_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3478_, 0, v_msg_3470_);
                        return v___x_3478_;
                    } else {
                        leanh::lean_inc_ref(v_env_3475_);
                        v___x_3479_ = l_Lean_Environment_setExporting(v_env_3475_, v___x_3476_);
                        leanh::lean_inc(v_declHint_3471_);
                        leanh::lean_inc_ref(v___x_3479_);
                        v___x_3480_ = l_Lean_Environment_contains(
                            v___x_3479_,
                            v_declHint_3471_,
                            v_isExporting_3477_,
                        );
                        if v___x_3480_ == 0 {
                            leanh::lean_dec_ref(v___x_3479_);
                            leanh::lean_dec_ref(v_env_3475_);
                            leanh::lean_dec(v_declHint_3471_);
                            v___x_3481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3481_, 0, v_msg_3470_);
                            return v___x_3481_;
                        } else {
                            v___x_3482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__2);
                            v___x_3483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__0_spec__0___closed__5);
                            v___x_3484_ = l_Lean_Options_empty;
                            v___x_3485_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3485_, 0, v___x_3479_);
                            leanh::lean_ctor_set(v___x_3485_, 1, v___x_3482_);
                            leanh::lean_ctor_set(v___x_3485_, 2, v___x_3483_);
                            leanh::lean_ctor_set(v___x_3485_, 3, v___x_3484_);
                            leanh::lean_inc(v_declHint_3471_);
                            v___x_3486_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3471_, v___x_3476_);
                            v_c_3487_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3487_, 0, v___x_3485_);
                            leanh::lean_ctor_set(v_c_3487_, 1, v___x_3486_);
                            v___x_3488_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3475_,
                                v_declHint_3471_,
                            );
                            if leanh::lean_obj_tag(v___x_3488_) == 0 {
                                leanh::lean_dec_ref(v_env_3475_);
                                leanh::lean_dec(v_declHint_3471_);
                                v___x_3489_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
                                v___x_3490_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3490_, 0, v___x_3489_);
                                leanh::lean_ctor_set(v___x_3490_, 1, v_c_3487_);
                                v___x_3491_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__3);
                                v___x_3492_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3492_, 0, v___x_3490_);
                                leanh::lean_ctor_set(v___x_3492_, 1, v___x_3491_);
                                v___x_3493_ = l_Lean_MessageData_note(v___x_3492_);
                                v___x_3494_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3494_, 0, v_msg_3470_);
                                leanh::lean_ctor_set(v___x_3494_, 1, v___x_3493_);
                                v___x_3495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3495_, 0, v___x_3494_);
                                return v___x_3495_;
                            } else {
                                v_val_3496_ = leanh::lean_ctor_get(v___x_3488_, 0);
                                v_isSharedCheck_3531_ =
                                    (!leanh::lean_is_exclusive(v___x_3488_)) as u8;
                                if v_isSharedCheck_3531_ == 0 {
                                    v___x_3498_ = v___x_3488_;
                                    v_isShared_3499_ = v_isSharedCheck_3531_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3496_);
                                    leanh::lean_dec(v___x_3488_);
                                    v___x_3498_ = leanh::lean_box(0);
                                    v_isShared_3499_ = v_isSharedCheck_3531_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3475_);
                    leanh::lean_dec(v_declHint_3471_);
                    v___x_3532_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3532_, 0, v_msg_3470_);
                    return v___x_3532_;
                }
            }
            1 => {
                v___x_3500_ = leanh::lean_box(0);
                v___x_3501_ = l_Lean_Environment_header(v_env_3475_);
                leanh::lean_dec_ref(v_env_3475_);
                v___x_3502_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3501_);
                v_mod_3503_ = lean_array_get(v___x_3500_, v___x_3502_, v_val_3496_);
                leanh::lean_dec(v_val_3496_);
                leanh::lean_dec_ref(v___x_3502_);
                v___x_3504_ = l_Lean_isPrivateName(v_declHint_3471_);
                leanh::lean_dec(v_declHint_3471_);
                if v___x_3504_ == 0 {
                    v___x_3505_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__5);
                    v___x_3506_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3506_, 0, v___x_3505_);
                    leanh::lean_ctor_set(v___x_3506_, 1, v_c_3487_);
                    v___x_3507_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__7);
                    v___x_3508_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3508_, 0, v___x_3506_);
                    leanh::lean_ctor_set(v___x_3508_, 1, v___x_3507_);
                    v___x_3509_ = l_Lean_MessageData_ofName(v_mod_3503_);
                    v___x_3510_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3510_, 0, v___x_3508_);
                    leanh::lean_ctor_set(v___x_3510_, 1, v___x_3509_);
                    v___x_3511_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__9);
                    v___x_3512_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3512_, 0, v___x_3510_);
                    leanh::lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                    v___x_3513_ = l_Lean_MessageData_note(v___x_3512_);
                    v___x_3514_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3514_, 0, v_msg_3470_);
                    leanh::lean_ctor_set(v___x_3514_, 1, v___x_3513_);
                    if v_isShared_3499_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3498_, 0);
                        leanh::lean_ctor_set(v___x_3498_, 0, v___x_3514_);
                        v___x_3516_ = v___x_3498_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3517_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
                        v___x_3516_ = v_reuseFailAlloc_3517_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3518_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__1);
                    v___x_3519_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3519_, 0, v___x_3518_);
                    leanh::lean_ctor_set(v___x_3519_, 1, v_c_3487_);
                    v___x_3520_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__11);
                    v___x_3521_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3521_, 0, v___x_3519_);
                    leanh::lean_ctor_set(v___x_3521_, 1, v___x_3520_);
                    v___x_3522_ = l_Lean_MessageData_ofName(v_mod_3503_);
                    v___x_3523_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3523_, 0, v___x_3521_);
                    leanh::lean_ctor_set(v___x_3523_, 1, v___x_3522_);
                    v___x_3524_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___closed__13);
                    v___x_3525_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3525_, 0, v___x_3523_);
                    leanh::lean_ctor_set(v___x_3525_, 1, v___x_3524_);
                    v___x_3526_ = l_Lean_MessageData_note(v___x_3525_);
                    v___x_3527_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3527_, 0, v_msg_3470_);
                    leanh::lean_ctor_set(v___x_3527_, 1, v___x_3526_);
                    if v_isShared_3499_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3498_, 0);
                        leanh::lean_ctor_set(v___x_3498_, 0, v___x_3527_);
                        v___x_3529_ = v___x_3498_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
                        v___x_3529_ = v_reuseFailAlloc_3530_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3516_;
            }
            3 => {
                return v___x_3529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg___boxed(
    mut v_msg_3533_: *mut leanh::LeanObject,
    mut v_declHint_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3537_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_3533_, v_declHint_3534_, v___y_3535_);
    leanh::lean_dec(v___y_3535_);
    return v_res_3537_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(
    mut v_msg_3538_: *mut leanh::LeanObject,
    mut v_declHint_3539_: *mut leanh::LeanObject,
    mut v___y_3540_: *mut leanh::LeanObject,
    mut v___y_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3551_: u8 = 0;
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3547_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_3538_, v_declHint_3539_, v___y_3545_);
                v_a_3548_ = leanh::lean_ctor_get(v___x_3547_, 0);
                v_isSharedCheck_3557_ = (!leanh::lean_is_exclusive(v___x_3547_)) as u8;
                if v_isSharedCheck_3557_ == 0 {
                    v___x_3550_ = v___x_3547_;
                    v_isShared_3551_ = v_isSharedCheck_3557_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3548_);
                    leanh::lean_dec(v___x_3547_);
                    v___x_3550_ = leanh::lean_box(0);
                    v_isShared_3551_ = v_isSharedCheck_3557_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3552_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3553_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3553_, 0, v___x_3552_);
                leanh::lean_ctor_set(v___x_3553_, 1, v_a_3548_);
                if v_isShared_3551_ == 0 {
                    leanh::lean_ctor_set(v___x_3550_, 0, v___x_3553_);
                    v___x_3555_ = v___x_3550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
                    v___x_3555_ = v_reuseFailAlloc_3556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3___boxed(
    mut v_msg_3558_: *mut leanh::LeanObject,
    mut v_declHint_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
    mut v___y_3563_: *mut leanh::LeanObject,
    mut v___y_3564_: *mut leanh::LeanObject,
    mut v___y_3565_: *mut leanh::LeanObject,
    mut v___y_3566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3567_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_3558_, v_declHint_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
    leanh::lean_dec(v___y_3565_);
    leanh::lean_dec_ref(v___y_3564_);
    leanh::lean_dec(v___y_3563_);
    leanh::lean_dec_ref(v___y_3562_);
    leanh::lean_dec(v___y_3561_);
    leanh::lean_dec_ref(v___y_3560_);
    return v_res_3567_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(
    mut v_ref_3568_: *mut leanh::LeanObject,
    mut v_msg_3569_: *mut leanh::LeanObject,
    mut v_declHint_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
    mut v___y_3572_: *mut leanh::LeanObject,
    mut v___y_3573_: *mut leanh::LeanObject,
    mut v___y_3574_: *mut leanh::LeanObject,
    mut v___y_3575_: *mut leanh::LeanObject,
    mut v___y_3576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3578_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3(v_msg_3569_, v_declHint_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
    v_a_3579_ = leanh::lean_ctor_get(v___x_3578_, 0);
    leanh::lean_inc(v_a_3579_);
    leanh::lean_dec_ref(v___x_3578_);
    v___x_3580_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_3568_, v_a_3579_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
    return v___x_3580_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg___boxed(
    mut v_ref_3581_: *mut leanh::LeanObject,
    mut v_msg_3582_: *mut leanh::LeanObject,
    mut v_declHint_3583_: *mut leanh::LeanObject,
    mut v___y_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_3581_, v_msg_3582_, v_declHint_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
    leanh::lean_dec(v___y_3589_);
    leanh::lean_dec_ref(v___y_3588_);
    leanh::lean_dec(v___y_3587_);
    leanh::lean_dec_ref(v___y_3586_);
    leanh::lean_dec(v___y_3585_);
    leanh::lean_dec_ref(v___y_3584_);
    leanh::lean_dec(v_ref_3581_);
    return v_res_3591_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(
    mut v_as_3592_: *mut leanh::LeanObject,
    mut v_k_3593_: *mut leanh::LeanObject,
    mut v_x_3594_: *mut leanh::LeanObject,
    mut v_x_3595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: u8 = 0;
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3596_ = lean_nat_add(v_x_3594_, v_x_3595_);
                v___x_3597_ = leanh::lean_unsigned_to_nat(1);
                v_m_3598_ = lean_nat_shiftr(v___x_3596_, v___x_3597_);
                leanh::lean_dec(v___x_3596_);
                v_a_3599_ = lean_array_fget_borrowed(v_as_3592_, v_m_3598_);
                v___x_3600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_a_3599_, v_k_3593_);
                if v___x_3600_ == 0 {
                    leanh::lean_dec(v_x_3595_);
                    v___x_3601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__3___redArg___lam__0(v_k_3593_, v_a_3599_);
                    if v___x_3601_ == 0 {
                        leanh::lean_dec(v_m_3598_);
                        leanh::lean_dec(v_x_3594_);
                        leanh::lean_inc(v_a_3599_);
                        v___x_3602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3602_, 0, v_a_3599_);
                        return v___x_3602_;
                    } else {
                        v___x_3603_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3604_ = lean_nat_dec_eq(v_m_3598_, v___x_3603_);
                        if v___x_3604_ == 0 {
                            v___x_3605_ = lean_nat_sub(v_m_3598_, v___x_3597_);
                            leanh::lean_dec(v_m_3598_);
                            v___x_3606_ = lean_nat_dec_lt(v___x_3605_, v_x_3594_);
                            if v___x_3606_ == 0 {
                                v_x_3595_ = v___x_3605_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3605_);
                                leanh::lean_dec(v_x_3594_);
                                v___x_3608_ = leanh::lean_box(0);
                                return v___x_3608_;
                            }
                        } else {
                            leanh::lean_dec(v_m_3598_);
                            leanh::lean_dec(v_x_3594_);
                            v___x_3609_ = leanh::lean_box(0);
                            return v___x_3609_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_3594_);
                    v___x_3610_ = lean_nat_add(v_m_3598_, v___x_3597_);
                    leanh::lean_dec(v_m_3598_);
                    v___x_3611_ = lean_nat_dec_le(v___x_3610_, v_x_3595_);
                    if v___x_3611_ == 0 {
                        leanh::lean_dec(v___x_3610_);
                        leanh::lean_dec(v_x_3595_);
                        v___x_3612_ = leanh::lean_box(0);
                        return v___x_3612_;
                    } else {
                        v_x_3594_ = v___x_3610_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg___boxed(
    mut v_as_3614_: *mut leanh::LeanObject,
    mut v_k_3615_: *mut leanh::LeanObject,
    mut v_x_3616_: *mut leanh::LeanObject,
    mut v_x_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_3614_, v_k_3615_, v_x_3616_, v_x_3617_);
    leanh::lean_dec_ref(v_k_3615_);
    leanh::lean_dec_ref(v_as_3614_);
    return v_res_3618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(
    mut v_incorrectName_3619_: *mut leanh::LeanObject,
    mut v_as_3620_: *mut leanh::LeanObject,
    mut v_i_3621_: usize,
    mut v_stop_3622_: usize,
    mut v_b_3623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: usize = 0;
    let mut v___x_3627_: usize = 0;
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: u8 = 0;
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: u8 = 0;
    let mut v___x_3644_: u8 = 0;
    let mut v___x_3645_: usize = 0;
    let mut v___x_3646_: usize = 0;
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: usize = 0;
    let mut v___x_3649_: usize = 0;
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3629_ = lean_usize_dec_eq(v_i_3621_, v_stop_3622_);
                if v___x_3629_ == 0 {
                    v___x_3630_ = lean_array_uget_borrowed(v_as_3620_, v_i_3621_);
                    v___x_3631_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3632_ = lean_array_get_size(v___x_3630_);
                    v___x_3633_ = lean_nat_dec_lt(v___x_3631_, v___x_3632_);
                    if v___x_3633_ == 0 {
                        v___y_3625_ = v_b_3623_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3634_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3635_ = lean_nat_sub(v___x_3632_, v___x_3634_);
                        v___x_3636_ = lean_nat_dec_le(v___x_3631_, v___x_3635_);
                        if v___x_3636_ == 0 {
                            leanh::lean_dec(v___x_3635_);
                            v___y_3625_ = v_b_3623_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3637_ = l_Lean_getSuggestions___redArg___lam__1___closed__0;
                            leanh::lean_inc(v_incorrectName_3619_);
                            v___x_3638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3638_, 0, v_incorrectName_3619_);
                            leanh::lean_ctor_set(v___x_3638_, 1, v___x_3637_);
                            v___x_3639_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v___x_3630_, v___x_3638_, v___x_3631_, v___x_3635_);
                            leanh::lean_dec_ref_known(v___x_3638_, 2);
                            if leanh::lean_obj_tag(v___x_3639_) == 0 {
                                v___y_3625_ = v_b_3623_;
                                state = 1;
                                continue;
                            } else {
                                v_val_3640_ = leanh::lean_ctor_get(v___x_3639_, 0);
                                leanh::lean_inc(v_val_3640_);
                                leanh::lean_dec_ref_known(v___x_3639_, 1);
                                v_snd_3641_ = leanh::lean_ctor_get(v_val_3640_, 1);
                                leanh::lean_inc(v_snd_3641_);
                                leanh::lean_dec(v_val_3640_);
                                v___x_3642_ = lean_array_get_size(v_snd_3641_);
                                v___x_3643_ = lean_nat_dec_lt(v___x_3631_, v___x_3642_);
                                if v___x_3643_ == 0 {
                                    leanh::lean_dec(v_snd_3641_);
                                    v___y_3625_ = v_b_3623_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3644_ = lean_nat_dec_le(v___x_3642_, v___x_3642_);
                                    if v___x_3644_ == 0 {
                                        if v___x_3643_ == 0 {
                                            leanh::lean_dec(v_snd_3641_);
                                            v___y_3625_ = v_b_3623_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_3645_ = 0usize;
                                            v___x_3646_ = lean_usize_of_nat(v___x_3642_);
                                            v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_3641_, v___x_3645_, v___x_3646_, v_b_3623_);
                                            leanh::lean_dec(v_snd_3641_);
                                            v___y_3625_ = v___x_3647_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___x_3648_ = 0usize;
                                        v___x_3649_ = lean_usize_of_nat(v___x_3642_);
                                        v___x_3650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__4(v_snd_3641_, v___x_3648_, v___x_3649_, v_b_3623_);
                                        leanh::lean_dec(v_snd_3641_);
                                        v___y_3625_ = v___x_3650_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_incorrectName_3619_);
                    return v_b_3623_;
                }
            }
            1 => {
                v___x_3626_ = 1usize;
                v___x_3627_ = lean_usize_add(v_i_3621_, v___x_3626_);
                v_i_3621_ = v___x_3627_;
                v_b_3623_ = v___y_3625_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1___boxed(
    mut v_incorrectName_3651_: *mut leanh::LeanObject,
    mut v_as_3652_: *mut leanh::LeanObject,
    mut v_i_3653_: *mut leanh::LeanObject,
    mut v_stop_3654_: *mut leanh::LeanObject,
    mut v_b_3655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3656_: usize = 0;
    let mut v_stop_boxed_3657_: usize = 0;
    let mut v_res_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3656_ = leanh::lean_unbox_usize(v_i_3653_);
    leanh::lean_dec(v_i_3653_);
    v_stop_boxed_3657_ = leanh::lean_unbox_usize(v_stop_3654_);
    leanh::lean_dec(v_stop_3654_);
    v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_3651_, v_as_3652_, v_i_boxed_3656_, v_stop_boxed_3657_, v_b_3655_);
    leanh::lean_dec_ref(v_as_3652_);
    return v_res_3658_;
}
pub unsafe fn l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(
    mut v_incorrectName_3659_: *mut leanh::LeanObject,
    mut v___y_3660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: u8 = 0;
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: u8 = 0;
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: usize = 0;
    let mut v___x_3682_: usize = 0;
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: usize = 0;
    let mut v___x_3686_: usize = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3662_ = lean_st_ref_get(v___y_3660_);
                v_env_3663_ = leanh::lean_ctor_get(v___x_3662_, 0);
                leanh::lean_inc_ref(v_env_3663_);
                leanh::lean_dec(v___x_3662_);
                v___x_3664_ =
                    l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl;
                v_snd_3665_ = leanh::lean_ctor_get(v___x_3664_, 1);
                v_toEnvExtension_3666_ = leanh::lean_ctor_get(v_snd_3665_, 0);
                v_asyncMode_3667_ = leanh::lean_ctor_get(v_toEnvExtension_3666_, 2);
                v___x_3668_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_getSuggestions___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_getSuggestions___redArg___closed__2_once),
                    _init_l_Lean_getSuggestions___redArg___closed__2,
                );
                v___x_3669_ = leanh::lean_box(0);
                v___x_3670_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_3668_,
                        v_toEnvExtension_3666_,
                        v_env_3663_,
                        v_asyncMode_3667_,
                        v___x_3669_,
                    );
                v_importedEntries_3671_ = leanh::lean_ctor_get(v___x_3670_, 0);
                leanh::lean_inc_ref(v_importedEntries_3671_);
                v_state_3672_ = leanh::lean_ctor_get(v___x_3670_, 1);
                leanh::lean_inc(v_state_3672_);
                leanh::lean_dec(v___x_3670_);
                v___x_3689_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_state_3672_, v_incorrectName_3659_);
                leanh::lean_dec(v_state_3672_);
                if leanh::lean_obj_tag(v___x_3689_) == 0 {
                    v___x_3690_ = l_Lean_NameSet_empty;
                    v___y_3674_ = v___x_3690_;
                    state = 1;
                    continue;
                } else {
                    v_val_3691_ = leanh::lean_ctor_get(v___x_3689_, 0);
                    leanh::lean_inc(v_val_3691_);
                    leanh::lean_dec_ref_known(v___x_3689_, 1);
                    v___y_3674_ = v_val_3691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3675_ = leanh::lean_unsigned_to_nat(0);
                v___x_3676_ = lean_array_get_size(v_importedEntries_3671_);
                v___x_3677_ = lean_nat_dec_lt(v___x_3675_, v___x_3676_);
                if v___x_3677_ == 0 {
                    leanh::lean_dec_ref(v_importedEntries_3671_);
                    leanh::lean_dec(v_incorrectName_3659_);
                    v___x_3678_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3678_, 0, v___y_3674_);
                    return v___x_3678_;
                } else {
                    v___x_3679_ = lean_nat_dec_le(v___x_3676_, v___x_3676_);
                    if v___x_3679_ == 0 {
                        if v___x_3677_ == 0 {
                            leanh::lean_dec_ref(v_importedEntries_3671_);
                            leanh::lean_dec(v_incorrectName_3659_);
                            v___x_3680_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3680_, 0, v___y_3674_);
                            return v___x_3680_;
                        } else {
                            v___x_3681_ = 0usize;
                            v___x_3682_ = lean_usize_of_nat(v___x_3676_);
                            v___x_3683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_3659_, v_importedEntries_3671_, v___x_3681_, v___x_3682_, v___y_3674_);
                            leanh::lean_dec_ref(v_importedEntries_3671_);
                            v___x_3684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3684_, 0, v___x_3683_);
                            return v___x_3684_;
                        }
                    } else {
                        v___x_3685_ = 0usize;
                        v___x_3686_ = lean_usize_of_nat(v___x_3676_);
                        v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__1(v_incorrectName_3659_, v_importedEntries_3671_, v___x_3685_, v___x_3686_, v___y_3674_);
                        leanh::lean_dec_ref(v_importedEntries_3671_);
                        v___x_3688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3688_, 0, v___x_3687_);
                        return v___x_3688_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg___boxed(
    mut v_incorrectName_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ =
        l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(
            v_incorrectName_3692_,
            v___y_3693_,
        );
    leanh::lean_dec(v___y_3693_);
    return v_res_3695_;
}
pub unsafe fn _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_throwUnknownNameWithSuggestions___redArg___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_throwUnknownNameWithSuggestions___redArg___closed__2;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3703_ = l_Lean_throwUnknownNameWithSuggestions___redArg___closed__4;
    v___x_3704_ = l_Lean_stringToMessageData(v___x_3703_);
    return v___x_3704_;
}
pub unsafe fn _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3706_ = l_Lean_throwUnknownNameWithSuggestions___redArg___closed__6;
    v___x_3707_ = l_Lean_stringToMessageData(v___x_3706_);
    return v___x_3707_;
}
pub unsafe fn _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3709_ = l_Lean_throwUnknownNameWithSuggestions___redArg___closed__8;
    v___x_3710_ = l_Lean_stringToMessageData(v___x_3709_);
    return v___x_3710_;
}
pub unsafe fn _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ = l_Lean_throwUnknownNameWithSuggestions___redArg___closed__10;
    v___x_3713_ = l_Lean_stringToMessageData(v___x_3712_);
    return v___x_3713_;
}
pub unsafe fn l_Lean_throwUnknownNameWithSuggestions___redArg(
    mut v_constName_3714_: *mut leanh::LeanObject,
    mut v_idOrConst_3715_: *mut leanh::LeanObject,
    mut v_declHint_3716_: *mut leanh::LeanObject,
    mut v_ref_x3f_3717_: *mut leanh::LeanObject,
    mut v_extraMsg_3718_: *mut leanh::LeanObject,
    mut v_a_3719_: *mut leanh::LeanObject,
    mut v_a_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
    mut v_a_3723_: *mut leanh::LeanObject,
    mut v_a_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hint_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3749_: u8 = 0;
    let mut v___y_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3763_: usize = 0;
    let mut v___x_3764_: usize = 0;
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3777_: u8 = 0;
    let mut v___y_3779_: u8 = 0;
    let mut v___y_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: u8 = 0;
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: u8 = 0;
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_constName_3714_);
                v___x_3795_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_constName_3714_, v_a_3724_);
                v_a_3796_ = leanh::lean_ctor_get(v___x_3795_, 0);
                leanh::lean_inc(v_a_3796_);
                leanh::lean_dec_ref(v___x_3795_);
                if leanh::lean_obj_tag(v_a_3796_) == 0 {
                    v_size_3824_ = leanh::lean_ctor_get(v_a_3796_, 0);
                    leanh::lean_inc(v_size_3824_);
                    v___y_3819_ = v_size_3824_;
                    state = 7;
                    continue;
                } else {
                    v___x_3825_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3819_ = v___x_3825_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_3735_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1_once
                    ),
                    _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__1,
                );
                v___x_3736_ = l_Lean_stringToMessageData(v_idOrConst_3715_);
                v___x_3737_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3737_, 0, v___x_3735_);
                leanh::lean_ctor_set(v___x_3737_, 1, v___x_3736_);
                v___x_3738_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3_once
                    ),
                    _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__3,
                );
                v___x_3739_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3739_, 0, v___x_3737_);
                leanh::lean_ctor_set(v___x_3739_, 1, v___x_3738_);
                v___x_3740_ = 0;
                v___x_3741_ = l_Lean_MessageData_ofConstName(v_constName_3714_, v___x_3740_);
                v___x_3742_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3742_, 0, v___x_3739_);
                leanh::lean_ctor_set(v___x_3742_, 1, v___x_3741_);
                v___x_3743_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
                v___x_3744_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3744_, 0, v___x_3742_);
                leanh::lean_ctor_set(v___x_3744_, 1, v___x_3743_);
                v___x_3745_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3745_, 0, v___x_3744_);
                leanh::lean_ctor_set(v___x_3745_, 1, v_extraMsg_3718_);
                v___x_3746_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3746_, 0, v___x_3745_);
                leanh::lean_ctor_set(v___x_3746_, 1, v_hint_3728_);
                v___x_3747_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v___y_3727_, v___x_3746_, v_declHint_3716_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
                leanh::lean_dec(v___y_3727_);
                return v___x_3747_;
            }
            2 => {
                v___x_3758_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5_once
                    ),
                    _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__5,
                );
                v___x_3759_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3759_, 0, v___x_3758_);
                leanh::lean_ctor_set(v___x_3759_, 1, v___y_3750_);
                v___x_3760_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3760_, 0, v___x_3759_);
                leanh::lean_ctor_set(v___x_3760_, 1, v___y_3757_);
                v___x_3761_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7_once
                    ),
                    _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__7,
                );
                v___x_3762_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3762_, 0, v___x_3760_);
                leanh::lean_ctor_set(v___x_3762_, 1, v___x_3761_);
                v_sz_3763_ = lean_array_size(v___y_3754_);
                v___x_3764_ = 0usize;
                leanh::lean_inc(v___y_3756_);
                leanh::lean_inc(v___y_3751_);
                v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_throwUnknownNameWithSuggestions_spec__2(v___y_3755_, v___y_3753_, v___y_3751_, v___y_3756_, v_sz_3763_, v___x_3764_, v___y_3754_);
                leanh::lean_dec(v___y_3755_);
                leanh::lean_inc(v___y_3752_);
                v___x_3766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3766_, 0, v___y_3752_);
                v___x_3767_ = leanh::lean_box(0);
                v___x_3768_ = l_Lean_MessageData_hint(
                    v___x_3762_,
                    v___x_3765_,
                    v___x_3766_,
                    v___x_3767_,
                    v___y_3749_,
                    v_a_3723_,
                    v_a_3724_,
                );
                leanh::lean_dec_ref(v___x_3765_);
                if leanh::lean_obj_tag(v___x_3768_) == 0 {
                    v_a_3769_ = leanh::lean_ctor_get(v___x_3768_, 0);
                    leanh::lean_inc(v_a_3769_);
                    leanh::lean_dec_ref_known(v___x_3768_, 1);
                    v___y_3727_ = v___y_3752_;
                    v_hint_3728_ = v_a_3769_;
                    v___y_3729_ = v_a_3719_;
                    v___y_3730_ = v_a_3720_;
                    v___y_3731_ = v_a_3721_;
                    v___y_3732_ = v_a_3722_;
                    v___y_3733_ = v_a_3723_;
                    v___y_3734_ = v_a_3724_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_3752_);
                    leanh::lean_dec_ref(v_extraMsg_3718_);
                    leanh::lean_dec(v_declHint_3716_);
                    leanh::lean_dec_ref(v_idOrConst_3715_);
                    leanh::lean_dec(v_constName_3714_);
                    v_a_3770_ = leanh::lean_ctor_get(v___x_3768_, 0);
                    v_isSharedCheck_3777_ = (!leanh::lean_is_exclusive(v___x_3768_)) as u8;
                    if v_isSharedCheck_3777_ == 0 {
                        v___x_3772_ = v___x_3768_;
                        v_isShared_3773_ = v_isSharedCheck_3777_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3770_);
                        leanh::lean_dec(v___x_3768_);
                        v___x_3772_ = leanh::lean_box(0);
                        v_isShared_3773_ = v_isSharedCheck_3777_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3773_ == 0 {
                    v___x_3775_ = v___x_3772_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3776_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
                    v___x_3775_ = v_reuseFailAlloc_3776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3775_;
            }
            5 => {
                v___x_3788_ = l_Lean_Name_isAnonymous(v___y_3782_);
                if v___x_3788_ == 0 {
                    v___x_3789_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9_once
                        ),
                        _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__9,
                    );
                    v___x_3790_ = l_Lean_MessageData_ofName(v___y_3782_);
                    v___x_3791_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3791_, 0, v___x_3789_);
                    leanh::lean_ctor_set(v___x_3791_, 1, v___x_3790_);
                    v___x_3792_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
                    v___x_3793_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3793_, 0, v___x_3791_);
                    leanh::lean_ctor_set(v___x_3793_, 1, v___x_3792_);
                    v___y_3749_ = v___y_3779_;
                    v___y_3750_ = v___y_3787_;
                    v___y_3751_ = v___y_3780_;
                    v___y_3752_ = v___y_3781_;
                    v___y_3753_ = v___y_3783_;
                    v___y_3754_ = v___y_3784_;
                    v___y_3755_ = v___y_3785_;
                    v___y_3756_ = v___y_3786_;
                    v___y_3757_ = v___x_3793_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_3782_);
                    v___x_3794_ = l_Lean_MessageData_nil;
                    v___y_3749_ = v___y_3779_;
                    v___y_3750_ = v___y_3787_;
                    v___y_3751_ = v___y_3780_;
                    v___y_3752_ = v___y_3781_;
                    v___y_3753_ = v___y_3783_;
                    v___y_3754_ = v___y_3784_;
                    v___y_3755_ = v___y_3785_;
                    v___y_3756_ = v___y_3786_;
                    v___y_3757_ = v___x_3794_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_3800_ = lean_array_get_size(v___y_3798_);
                v___x_3801_ = leanh::lean_unsigned_to_nat(0);
                v___x_3802_ = lean_nat_dec_eq(v___x_3800_, v___x_3801_);
                if v___x_3802_ == 0 {
                    v___x_3803_ = lean_st_ref_get(v_a_3724_);
                    v_env_3804_ = leanh::lean_ctor_get(v___x_3803_, 0);
                    leanh::lean_inc_ref(v_env_3804_);
                    leanh::lean_dec(v___x_3803_);
                    v_currNamespace_3805_ = leanh::lean_ctor_get(v_a_3723_, 6);
                    v_openDecls_3806_ = leanh::lean_ctor_get(v_a_3723_, 7);
                    v___x_3807_ = l_Lean_Syntax_getId(v___y_3799_);
                    leanh::lean_inc(v_constName_3714_);
                    v___x_3808_ = l_Lean_Name_eraseSuffix_x3f(v_constName_3714_, v___x_3807_);
                    v___x_3809_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3810_ = lean_nat_dec_eq(v___x_3800_, v___x_3809_);
                    if v___x_3810_ == 0 {
                        v___x_3811_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11_once
                            ),
                            _init_l_Lean_throwUnknownNameWithSuggestions___redArg___closed__11,
                        );
                        v___y_3779_ = v___x_3802_;
                        v___y_3780_ = v_currNamespace_3805_;
                        v___y_3781_ = v___y_3799_;
                        v___y_3782_ = v___x_3807_;
                        v___y_3783_ = v_env_3804_;
                        v___y_3784_ = v___y_3798_;
                        v___y_3785_ = v___x_3808_;
                        v___y_3786_ = v_openDecls_3806_;
                        v___y_3787_ = v___x_3811_;
                        state = 5;
                        continue;
                    } else {
                        v___x_3812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
                        v___x_3813_ = lean_array_fget_borrowed(v___y_3798_, v___x_3801_);
                        leanh::lean_inc(v___x_3813_);
                        v___x_3814_ = l_Lean_MessageData_ofConstName(v___x_3813_, v___x_3802_);
                        v___x_3815_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3815_, 0, v___x_3812_);
                        leanh::lean_ctor_set(v___x_3815_, 1, v___x_3814_);
                        v___x_3816_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3816_, 0, v___x_3815_);
                        leanh::lean_ctor_set(v___x_3816_, 1, v___x_3812_);
                        v___y_3779_ = v___x_3802_;
                        v___y_3780_ = v_currNamespace_3805_;
                        v___y_3781_ = v___y_3799_;
                        v___y_3782_ = v___x_3807_;
                        v___y_3783_ = v_env_3804_;
                        v___y_3784_ = v___y_3798_;
                        v___y_3785_ = v___x_3808_;
                        v___y_3786_ = v_openDecls_3806_;
                        v___y_3787_ = v___x_3816_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3798_);
                    v___x_3817_ = l_Lean_MessageData_nil;
                    v___y_3727_ = v___y_3799_;
                    v_hint_3728_ = v___x_3817_;
                    v___y_3729_ = v_a_3719_;
                    v___y_3730_ = v_a_3720_;
                    v___y_3731_ = v_a_3721_;
                    v___y_3732_ = v_a_3722_;
                    v___y_3733_ = v_a_3723_;
                    v___y_3734_ = v_a_3724_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_3820_ = lean_mk_empty_array_with_capacity(v___y_3819_);
                leanh::lean_dec(v___y_3819_);
                v___x_3821_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_IdentifierSuggestion_0__Lean_mkExistingToIncorrect_spec__0_spec__0(v___x_3820_, v_a_3796_);
                if leanh::lean_obj_tag(v_ref_x3f_3717_) == 0 {
                    v_ref_3822_ = leanh::lean_ctor_get(v_a_3723_, 5);
                    leanh::lean_inc(v_ref_3822_);
                    v___y_3798_ = v___x_3821_;
                    v___y_3799_ = v_ref_3822_;
                    state = 6;
                    continue;
                } else {
                    v_val_3823_ = leanh::lean_ctor_get(v_ref_x3f_3717_, 0);
                    leanh::lean_inc(v_val_3823_);
                    leanh::lean_dec_ref_known(v_ref_x3f_3717_, 1);
                    v___y_3798_ = v___x_3821_;
                    v___y_3799_ = v_val_3823_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwUnknownNameWithSuggestions___redArg___boxed(
    mut v_constName_3826_: *mut leanh::LeanObject,
    mut v_idOrConst_3827_: *mut leanh::LeanObject,
    mut v_declHint_3828_: *mut leanh::LeanObject,
    mut v_ref_x3f_3829_: *mut leanh::LeanObject,
    mut v_extraMsg_3830_: *mut leanh::LeanObject,
    mut v_a_3831_: *mut leanh::LeanObject,
    mut v_a_3832_: *mut leanh::LeanObject,
    mut v_a_3833_: *mut leanh::LeanObject,
    mut v_a_3834_: *mut leanh::LeanObject,
    mut v_a_3835_: *mut leanh::LeanObject,
    mut v_a_3836_: *mut leanh::LeanObject,
    mut v_a_3837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3838_ = l_Lean_throwUnknownNameWithSuggestions___redArg(
        v_constName_3826_,
        v_idOrConst_3827_,
        v_declHint_3828_,
        v_ref_x3f_3829_,
        v_extraMsg_3830_,
        v_a_3831_,
        v_a_3832_,
        v_a_3833_,
        v_a_3834_,
        v_a_3835_,
        v_a_3836_,
    );
    leanh::lean_dec(v_a_3836_);
    leanh::lean_dec_ref(v_a_3835_);
    leanh::lean_dec(v_a_3834_);
    leanh::lean_dec_ref(v_a_3833_);
    leanh::lean_dec(v_a_3832_);
    leanh::lean_dec_ref(v_a_3831_);
    return v_res_3838_;
}
pub unsafe fn l_Lean_throwUnknownNameWithSuggestions(
    mut v_00_u03b1_3839_: *mut leanh::LeanObject,
    mut v_constName_3840_: *mut leanh::LeanObject,
    mut v_idOrConst_3841_: *mut leanh::LeanObject,
    mut v_declHint_3842_: *mut leanh::LeanObject,
    mut v_ref_x3f_3843_: *mut leanh::LeanObject,
    mut v_extraMsg_3844_: *mut leanh::LeanObject,
    mut v_a_3845_: *mut leanh::LeanObject,
    mut v_a_3846_: *mut leanh::LeanObject,
    mut v_a_3847_: *mut leanh::LeanObject,
    mut v_a_3848_: *mut leanh::LeanObject,
    mut v_a_3849_: *mut leanh::LeanObject,
    mut v_a_3850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3852_ = l_Lean_throwUnknownNameWithSuggestions___redArg(
        v_constName_3840_,
        v_idOrConst_3841_,
        v_declHint_3842_,
        v_ref_x3f_3843_,
        v_extraMsg_3844_,
        v_a_3845_,
        v_a_3846_,
        v_a_3847_,
        v_a_3848_,
        v_a_3849_,
        v_a_3850_,
    );
    return v___x_3852_;
}
pub unsafe fn l_Lean_throwUnknownNameWithSuggestions___boxed(
    mut v_00_u03b1_3853_: *mut leanh::LeanObject,
    mut v_constName_3854_: *mut leanh::LeanObject,
    mut v_idOrConst_3855_: *mut leanh::LeanObject,
    mut v_declHint_3856_: *mut leanh::LeanObject,
    mut v_ref_x3f_3857_: *mut leanh::LeanObject,
    mut v_extraMsg_3858_: *mut leanh::LeanObject,
    mut v_a_3859_: *mut leanh::LeanObject,
    mut v_a_3860_: *mut leanh::LeanObject,
    mut v_a_3861_: *mut leanh::LeanObject,
    mut v_a_3862_: *mut leanh::LeanObject,
    mut v_a_3863_: *mut leanh::LeanObject,
    mut v_a_3864_: *mut leanh::LeanObject,
    mut v_a_3865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3866_ = l_Lean_throwUnknownNameWithSuggestions(
        v_00_u03b1_3853_,
        v_constName_3854_,
        v_idOrConst_3855_,
        v_declHint_3856_,
        v_ref_x3f_3857_,
        v_extraMsg_3858_,
        v_a_3859_,
        v_a_3860_,
        v_a_3861_,
        v_a_3862_,
        v_a_3863_,
        v_a_3864_,
    );
    leanh::lean_dec(v_a_3864_);
    leanh::lean_dec_ref(v_a_3863_);
    leanh::lean_dec(v_a_3862_);
    leanh::lean_dec_ref(v_a_3861_);
    leanh::lean_dec(v_a_3860_);
    leanh::lean_dec_ref(v_a_3859_);
    return v_res_3866_;
}
pub unsafe fn l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(
    mut v_incorrectName_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
    mut v___y_3869_: *mut leanh::LeanObject,
    mut v___y_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ =
        l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(
            v_incorrectName_3867_,
            v___y_3873_,
        );
    return v___x_3875_;
}
pub unsafe fn l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___boxed(
    mut v_incorrectName_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
    mut v___y_3879_: *mut leanh::LeanObject,
    mut v___y_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
    mut v___y_3882_: *mut leanh::LeanObject,
    mut v___y_3883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3884_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0(
        v_incorrectName_3876_,
        v___y_3877_,
        v___y_3878_,
        v___y_3879_,
        v___y_3880_,
        v___y_3881_,
        v___y_3882_,
    );
    leanh::lean_dec(v___y_3882_);
    leanh::lean_dec_ref(v___y_3881_);
    leanh::lean_dec(v___y_3880_);
    leanh::lean_dec_ref(v___y_3879_);
    leanh::lean_dec(v___y_3878_);
    leanh::lean_dec_ref(v___y_3877_);
    return v_res_3884_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(
    mut v_00_u03b1_3885_: *mut leanh::LeanObject,
    mut v_ref_3886_: *mut leanh::LeanObject,
    mut v_msg_3887_: *mut leanh::LeanObject,
    mut v_declHint_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
    mut v___y_3892_: *mut leanh::LeanObject,
    mut v___y_3893_: *mut leanh::LeanObject,
    mut v___y_3894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___redArg(v_ref_3886_, v_msg_3887_, v_declHint_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
    return v___x_3896_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1___boxed(
    mut v_00_u03b1_3897_: *mut leanh::LeanObject,
    mut v_ref_3898_: *mut leanh::LeanObject,
    mut v_msg_3899_: *mut leanh::LeanObject,
    mut v_declHint_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3908_ =
        l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1(
            v_00_u03b1_3897_,
            v_ref_3898_,
            v_msg_3899_,
            v_declHint_3900_,
            v___y_3901_,
            v___y_3902_,
            v___y_3903_,
            v___y_3904_,
            v___y_3905_,
            v___y_3906_,
        );
    leanh::lean_dec(v___y_3906_);
    leanh::lean_dec_ref(v___y_3905_);
    leanh::lean_dec(v___y_3904_);
    leanh::lean_dec_ref(v___y_3903_);
    leanh::lean_dec(v___y_3902_);
    leanh::lean_dec_ref(v___y_3901_);
    leanh::lean_dec(v_ref_3898_);
    return v_res_3908_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(
    mut v_as_3909_: *mut leanh::LeanObject,
    mut v_k_3910_: *mut leanh::LeanObject,
    mut v_x_3911_: *mut leanh::LeanObject,
    mut v_x_3912_: *mut leanh::LeanObject,
    mut v_x_3913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___redArg(v_as_3909_, v_k_3910_, v_x_3911_, v_x_3912_);
    return v___x_3914_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0___boxed(
    mut v_as_3915_: *mut leanh::LeanObject,
    mut v_k_3916_: *mut leanh::LeanObject,
    mut v_x_3917_: *mut leanh::LeanObject,
    mut v_x_3918_: *mut leanh::LeanObject,
    mut v_x_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3920_ = l_Array_binSearchAux___at___00Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0_spec__0(v_as_3915_, v_k_3916_, v_x_3917_, v_x_3918_, v_x_3919_);
    leanh::lean_dec_ref(v_k_3916_);
    leanh::lean_dec_ref(v_as_3915_);
    return v_res_3920_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(
    mut v_msg_3921_: *mut leanh::LeanObject,
    mut v_declHint_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
    mut v___y_3926_: *mut leanh::LeanObject,
    mut v___y_3927_: *mut leanh::LeanObject,
    mut v___y_3928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___redArg(v_msg_3921_, v_declHint_3922_, v___y_3928_);
    return v___x_3930_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4___boxed(
    mut v_msg_3931_: *mut leanh::LeanObject,
    mut v_declHint_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
    mut v___y_3938_: *mut leanh::LeanObject,
    mut v___y_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3940_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__3_spec__4(v_msg_3931_, v_declHint_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
    leanh::lean_dec(v___y_3938_);
    leanh::lean_dec_ref(v___y_3937_);
    leanh::lean_dec(v___y_3936_);
    leanh::lean_dec_ref(v___y_3935_);
    leanh::lean_dec(v___y_3934_);
    leanh::lean_dec_ref(v___y_3933_);
    return v_res_3940_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(
    mut v_00_u03b1_3941_: *mut leanh::LeanObject,
    mut v_ref_3942_: *mut leanh::LeanObject,
    mut v_msg_3943_: *mut leanh::LeanObject,
    mut v___y_3944_: *mut leanh::LeanObject,
    mut v___y_3945_: *mut leanh::LeanObject,
    mut v___y_3946_: *mut leanh::LeanObject,
    mut v___y_3947_: *mut leanh::LeanObject,
    mut v___y_3948_: *mut leanh::LeanObject,
    mut v___y_3949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___redArg(v_ref_3942_, v_msg_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
    return v___x_3951_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4___boxed(
    mut v_00_u03b1_3952_: *mut leanh::LeanObject,
    mut v_ref_3953_: *mut leanh::LeanObject,
    mut v_msg_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
    mut v___y_3957_: *mut leanh::LeanObject,
    mut v___y_3958_: *mut leanh::LeanObject,
    mut v___y_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
    mut v___y_3961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3962_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4(v_00_u03b1_3952_, v_ref_3953_, v_msg_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
    leanh::lean_dec(v___y_3960_);
    leanh::lean_dec_ref(v___y_3959_);
    leanh::lean_dec(v___y_3958_);
    leanh::lean_dec_ref(v___y_3957_);
    leanh::lean_dec(v___y_3956_);
    leanh::lean_dec_ref(v___y_3955_);
    leanh::lean_dec(v_ref_3953_);
    return v_res_3962_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(
    mut v_00_u03b1_3963_: *mut leanh::LeanObject,
    mut v_msg_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
    mut v___y_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___redArg(v_msg_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
    return v___x_3972_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_3973_: *mut leanh::LeanObject,
    mut v_msg_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3982_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6(v_00_u03b1_3973_, v_msg_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
    leanh::lean_dec(v___y_3980_);
    leanh::lean_dec_ref(v___y_3979_);
    leanh::lean_dec(v___y_3978_);
    leanh::lean_dec_ref(v___y_3977_);
    leanh::lean_dec(v___y_3976_);
    leanh::lean_dec_ref(v___y_3975_);
    return v_res_3982_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(
    mut v_msgData_3983_: *mut leanh::LeanObject,
    mut v_macroStack_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
    mut v___y_3990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___redArg(v_msgData_3983_, v_macroStack_3984_, v___y_3989_);
    return v___x_3992_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9___boxed(
    mut v_msgData_3993_: *mut leanh::LeanObject,
    mut v_macroStack_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
    mut v___y_3996_: *mut leanh::LeanObject,
    mut v___y_3997_: *mut leanh::LeanObject,
    mut v___y_3998_: *mut leanh::LeanObject,
    mut v___y_3999_: *mut leanh::LeanObject,
    mut v___y_4000_: *mut leanh::LeanObject,
    mut v___y_4001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4002_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9(v_msgData_3993_, v_macroStack_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
    leanh::lean_dec(v___y_4000_);
    leanh::lean_dec_ref(v___y_3999_);
    leanh::lean_dec(v___y_3998_);
    leanh::lean_dec_ref(v___y_3997_);
    leanh::lean_dec(v___y_3996_);
    leanh::lean_dec_ref(v___y_3995_);
    return v_res_4002_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(
    mut v_exp_4003_: *mut leanh::LeanObject,
    mut v_as_4004_: *mut leanh::LeanObject,
    mut v_i_4005_: usize,
    mut v_stop_4006_: usize,
) -> u8 {
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: u8 = 0;
    let mut v___x_4010_: usize = 0;
    let mut v___x_4011_: usize = 0;
    let mut v___x_4013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4007_ = lean_usize_dec_eq(v_i_4005_, v_stop_4006_);
                if v___x_4007_ == 0 {
                    v___x_4008_ = lean_array_uget_borrowed(v_as_4004_, v_i_4005_);
                    v___x_4009_ = lean_expr_eqv(v___x_4008_, v_exp_4003_);
                    if v___x_4009_ == 0 {
                        v___x_4010_ = 1usize;
                        v___x_4011_ = lean_usize_add(v_i_4005_, v___x_4010_);
                        v_i_4005_ = v___x_4011_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4009_;
                    }
                } else {
                    v___x_4013_ = 0;
                    return v___x_4013_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1___boxed(
    mut v_exp_4014_: *mut leanh::LeanObject,
    mut v_as_4015_: *mut leanh::LeanObject,
    mut v_i_4016_: *mut leanh::LeanObject,
    mut v_stop_4017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4018_: usize = 0;
    let mut v_stop_boxed_4019_: usize = 0;
    let mut v_res_4020_: u8 = 0;
    let mut v_r_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4018_ = leanh::lean_unbox_usize(v_i_4016_);
    leanh::lean_dec(v_i_4016_);
    v_stop_boxed_4019_ = leanh::lean_unbox_usize(v_stop_4017_);
    leanh::lean_dec(v_stop_4017_);
    v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_4014_, v_as_4015_, v_i_boxed_4018_, v_stop_boxed_4019_);
    leanh::lean_dec_ref(v_as_4015_);
    leanh::lean_dec_ref(v_exp_4014_);
    v_r_4021_ = leanh::lean_box((v_res_4020_) as usize);
    return v_r_4021_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(
    mut v_exp_4022_: *mut leanh::LeanObject,
    mut v_x_4023_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4023_) == 0 {
        let mut v_cs_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4027_: u8 = 0;
        v_cs_4024_ = leanh::lean_ctor_get(v_x_4023_, 0);
        v___x_4025_ = leanh::lean_unsigned_to_nat(0);
        v___x_4026_ = lean_array_get_size(v_cs_4024_);
        v___x_4027_ = lean_nat_dec_lt(v___x_4025_, v___x_4026_);
        if v___x_4027_ == 0 {
            return v___x_4027_;
        } else {
            if v___x_4027_ == 0 {
                return v___x_4027_;
            } else {
                let mut v___x_4028_: usize = 0;
                let mut v___x_4029_: usize = 0;
                let mut v___x_4030_: u8 = 0;
                v___x_4028_ = 0usize;
                v___x_4029_ = lean_usize_of_nat(v___x_4026_);
                v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_4022_, v_cs_4024_, v___x_4028_, v___x_4029_);
                return v___x_4030_;
            }
        }
    } else {
        let mut v_vs_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4034_: u8 = 0;
        v_vs_4031_ = leanh::lean_ctor_get(v_x_4023_, 0);
        v___x_4032_ = leanh::lean_unsigned_to_nat(0);
        v___x_4033_ = lean_array_get_size(v_vs_4031_);
        v___x_4034_ = lean_nat_dec_lt(v___x_4032_, v___x_4033_);
        if v___x_4034_ == 0 {
            return v___x_4034_;
        } else {
            if v___x_4034_ == 0 {
                return v___x_4034_;
            } else {
                let mut v___x_4035_: usize = 0;
                let mut v___x_4036_: usize = 0;
                let mut v___x_4037_: u8 = 0;
                v___x_4035_ = 0usize;
                v___x_4036_ = lean_usize_of_nat(v___x_4033_);
                v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_4022_, v_vs_4031_, v___x_4035_, v___x_4036_);
                return v___x_4037_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(
    mut v_exp_4038_: *mut leanh::LeanObject,
    mut v_as_4039_: *mut leanh::LeanObject,
    mut v_i_4040_: usize,
    mut v_stop_4041_: usize,
) -> u8 {
    let mut v___x_4042_: u8 = 0;
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: u8 = 0;
    let mut v___x_4045_: usize = 0;
    let mut v___x_4046_: usize = 0;
    let mut v___x_4048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4042_ = lean_usize_dec_eq(v_i_4040_, v_stop_4041_);
                if v___x_4042_ == 0 {
                    v___x_4043_ = lean_array_uget_borrowed(v_as_4039_, v_i_4040_);
                    v___x_4044_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_4038_, v___x_4043_);
                    if v___x_4044_ == 0 {
                        v___x_4045_ = 1usize;
                        v___x_4046_ = lean_usize_add(v_i_4040_, v___x_4045_);
                        v_i_4040_ = v___x_4046_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4044_;
                    }
                } else {
                    v___x_4048_ = 0;
                    return v___x_4048_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1___boxed(
    mut v_exp_4049_: *mut leanh::LeanObject,
    mut v_as_4050_: *mut leanh::LeanObject,
    mut v_i_4051_: *mut leanh::LeanObject,
    mut v_stop_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4053_: usize = 0;
    let mut v_stop_boxed_4054_: usize = 0;
    let mut v_res_4055_: u8 = 0;
    let mut v_r_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4053_ = leanh::lean_unbox_usize(v_i_4051_);
    leanh::lean_dec(v_i_4051_);
    v_stop_boxed_4054_ = leanh::lean_unbox_usize(v_stop_4052_);
    leanh::lean_dec(v_stop_4052_);
    v_res_4055_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0_spec__1(v_exp_4049_, v_as_4050_, v_i_boxed_4053_, v_stop_boxed_4054_);
    leanh::lean_dec_ref(v_as_4050_);
    leanh::lean_dec_ref(v_exp_4049_);
    v_r_4056_ = leanh::lean_box((v_res_4055_) as usize);
    return v_r_4056_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0___boxed(
    mut v_exp_4057_: *mut leanh::LeanObject,
    mut v_x_4058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4059_: u8 = 0;
    let mut v_r_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4059_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_4057_, v_x_4058_);
    leanh::lean_dec_ref(v_x_4058_);
    leanh::lean_dec_ref(v_exp_4057_);
    v_r_4060_ = leanh::lean_box((v_res_4059_) as usize);
    return v_r_4060_;
}
pub unsafe fn l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(
    mut v_exp_4061_: *mut leanh::LeanObject,
    mut v_t_4062_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_root_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    v_root_4063_ = leanh::lean_ctor_get(v_t_4062_, 0);
    v_tail_4064_ = leanh::lean_ctor_get(v_t_4062_, 1);
    v___x_4065_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__0(v_exp_4061_, v_root_4063_);
    if v___x_4065_ == 0 {
        let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: u8 = 0;
        v___x_4066_ = leanh::lean_unsigned_to_nat(0);
        v___x_4067_ = lean_array_get_size(v_tail_4064_);
        v___x_4068_ = lean_nat_dec_lt(v___x_4066_, v___x_4067_);
        if v___x_4068_ == 0 {
            return v___x_4065_;
        } else {
            if v___x_4068_ == 0 {
                return v___x_4065_;
            } else {
                let mut v___x_4069_: usize = 0;
                let mut v___x_4070_: usize = 0;
                let mut v___x_4071_: u8 = 0;
                v___x_4069_ = 0usize;
                v___x_4070_ = lean_usize_of_nat(v___x_4067_);
                v___x_4071_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0_spec__1(v_exp_4061_, v_tail_4064_, v___x_4069_, v___x_4070_);
                return v___x_4071_;
            }
        }
    } else {
        return v___x_4065_;
    }
}
pub unsafe fn l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0___boxed(
    mut v_exp_4072_: *mut leanh::LeanObject,
    mut v_t_4073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4074_: u8 = 0;
    let mut v_r_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4074_ =
        l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(
            v_exp_4072_,
            v_t_4073_,
        );
    leanh::lean_dec_ref(v_t_4073_);
    leanh::lean_dec_ref(v_exp_4072_);
    v_r_4075_ = leanh::lean_box((v_res_4074_) as usize);
    return v_r_4075_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(
    mut v_init_4076_: *mut leanh::LeanObject,
    mut v_x_4077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4077_) == 0 {
                    v_k_4078_ = leanh::lean_ctor_get(v_x_4077_, 1);
                    v_l_4079_ = leanh::lean_ctor_get(v_x_4077_, 3);
                    v_r_4080_ = leanh::lean_ctor_get(v_x_4077_, 4);
                    v___x_4081_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v_init_4076_, v_r_4080_);
                    leanh::lean_inc(v_k_4078_);
                    v___x_4082_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4082_, 0, v_k_4078_);
                    leanh::lean_ctor_set(v___x_4082_, 1, v___x_4081_);
                    v_init_4076_ = v___x_4082_;
                    v_x_4077_ = v_l_4079_;
                    state = 0;
                    continue;
                } else {
                    return v_init_4076_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1___boxed(
    mut v_init_4084_: *mut leanh::LeanObject,
    mut v_x_4085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(
            v_init_4084_,
            v_x_4085_,
        );
    leanh::lean_dec(v_x_4085_);
    return v_res_4086_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4088_ =
        l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__0;
    v___x_4089_ = l_Lean_stringToMessageData(v___x_4088_);
    return v___x_4089_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(
    mut v_a_4090_: *mut leanh::LeanObject,
    mut v_a_4091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4097_: u8 = 0;
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4090_) == 0 {
                    v___x_4092_ = l_List_reverse___redArg(v_a_4091_);
                    return v___x_4092_;
                } else {
                    v_head_4093_ = leanh::lean_ctor_get(v_a_4090_, 0);
                    v_tail_4094_ = leanh::lean_ctor_get(v_a_4090_, 1);
                    v_isSharedCheck_4109_ = (!leanh::lean_is_exclusive(v_a_4090_)) as u8;
                    if v_isSharedCheck_4109_ == 0 {
                        v___x_4096_ = v_a_4090_;
                        v_isShared_4097_ = v_isSharedCheck_4109_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4094_);
                        leanh::lean_inc(v_head_4093_);
                        leanh::lean_dec(v_a_4090_);
                        v___x_4096_ = leanh::lean_box(0);
                        v_isShared_4097_ = v_isSharedCheck_4109_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4098_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2___closed__1);
                v___x_4099_ = 0;
                v___x_4100_ = l_Lean_MessageData_ofConstName(v_head_4093_, v___x_4099_);
                v___x_4101_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4101_, 0, v___x_4098_);
                leanh::lean_ctor_set(v___x_4101_, 1, v___x_4100_);
                v___x_4102_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2__spec__2___redArg___closed__5);
                v___x_4103_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4103_, 0, v___x_4101_);
                leanh::lean_ctor_set(v___x_4103_, 1, v___x_4102_);
                v___x_4104_ = l_Lean_indentD(v___x_4103_);
                if v_isShared_4097_ == 0 {
                    leanh::lean_ctor_set(v___x_4096_, 1, v_a_4091_);
                    leanh::lean_ctor_set(v___x_4096_, 0, v___x_4104_);
                    v___x_4106_ = v___x_4096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4108_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_a_4091_);
                    v___x_4106_ = v_reuseFailAlloc_4108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4090_ = v_tail_4094_;
                v_a_4091_ = v___x_4106_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4111_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__0;
    v___x_4112_ = l_Lean_stringToMessageData(v___x_4111_);
    return v___x_4112_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__2;
    v___x_4115_ = l_Lean_stringToMessageData(v___x_4114_);
    return v___x_4115_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4117_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__4;
    v___x_4118_ = l_Lean_stringToMessageData(v___x_4117_);
    return v___x_4118_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4120_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__6;
    v___x_4121_ = l_Lean_stringToMessageData(v___x_4120_);
    return v___x_4121_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownNameWithSuggestions_spec__1_spec__4_spec__6_spec__9_spec__11___closed__0);
    v___x_4123_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4123_, 0, v___x_4122_);
    leanh::lean_ctor_set(v___x_4123_, 1, v___x_4122_);
    return v___x_4123_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4125_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__9;
    v___x_4126_ = l_Lean_stringToMessageData(v___x_4125_);
    return v___x_4126_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__11;
    v___x_4129_ = l_Lean_stringToMessageData(v___x_4128_);
    return v___x_4129_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4131_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__13;
    v___x_4132_ = l_Lean_stringToMessageData(v___x_4131_);
    return v___x_4132_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4134_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__15;
    v___x_4135_ = l_Lean_stringToMessageData(v___x_4134_);
    return v___x_4135_;
}
pub unsafe fn _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__17;
    v___x_4138_ = l_Lean_stringToMessageData(v___x_4137_);
    return v___x_4138_;
}
pub unsafe fn l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(
    mut v_exp_4139_: *mut leanh::LeanObject,
    mut v_expected_4140_: *mut leanh::LeanObject,
    mut v_a_4141_: *mut leanh::LeanObject,
    mut v_a_4142_: *mut leanh::LeanObject,
    mut v_a_4143_: *mut leanh::LeanObject,
    mut v_a_4144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitContext_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: u8 = 0;
    let mut v_boundVariables_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_unused_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4214_: u8 = 0;
    let mut v_a_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4218_: u8 = 0;
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_autoBoundImplicitContext_4149_ = leanh::lean_ctor_get(v_a_4141_, 2);
                if leanh::lean_obj_tag(v_autoBoundImplicitContext_4149_) == 0 {
                    leanh::lean_dec_ref(v_expected_4140_);
                    state = 1;
                    continue;
                } else {
                    v_val_4150_ = leanh::lean_ctor_get(v_autoBoundImplicitContext_4149_, 0);
                    v___x_4151_ = l_Lean_Expr_isFVar(v_exp_4139_);
                    if v___x_4151_ == 0 {
                        leanh::lean_dec_ref(v_expected_4140_);
                        state = 1;
                        continue;
                    } else {
                        v_boundVariables_4152_ = leanh::lean_ctor_get(v_val_4150_, 0);
                        v___x_4153_ = l_Lean_PersistentArray_anyM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__0(v_exp_4139_, v_boundVariables_4152_);
                        if v___x_4153_ == 0 {
                            leanh::lean_dec_ref(v_expected_4140_);
                            state = 1;
                            continue;
                        } else {
                            v___x_4154_ = l_Lean_Expr_fvarId_x21(v_exp_4139_);
                            v___x_4155_ = l_Lean_FVarId_getUserName___redArg(
                                v___x_4154_,
                                v_a_4142_,
                                v_a_4143_,
                                v_a_4144_,
                            );
                            if leanh::lean_obj_tag(v___x_4155_) == 0 {
                                v_a_4156_ = leanh::lean_ctor_get(v___x_4155_, 0);
                                leanh::lean_inc_n(v_a_4156_, 2);
                                leanh::lean_dec_ref_known(v___x_4155_, 1);
                                v___x_4157_ = l_Lean_MessageData_ofName(v_a_4156_);
                                v___x_4158_ = l_Lean_getSuggestions___at___00Lean_throwUnknownNameWithSuggestions_spec__0___redArg(v_a_4156_, v_a_4144_);
                                v_a_4159_ = leanh::lean_ctor_get(v___x_4158_, 0);
                                v_isSharedCheck_4214_ =
                                    (!leanh::lean_is_exclusive(v___x_4158_)) as u8;
                                if v_isSharedCheck_4214_ == 0 {
                                    v___x_4161_ = v___x_4158_;
                                    v_isShared_4162_ = v_isSharedCheck_4214_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4159_);
                                    leanh::lean_dec(v___x_4158_);
                                    v___x_4161_ = leanh::lean_box(0);
                                    v_isShared_4162_ = v_isSharedCheck_4214_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_expected_4140_);
                                v_a_4215_ = leanh::lean_ctor_get(v___x_4155_, 0);
                                v_isSharedCheck_4222_ =
                                    (!leanh::lean_is_exclusive(v___x_4155_)) as u8;
                                if v_isSharedCheck_4222_ == 0 {
                                    v___x_4217_ = v___x_4155_;
                                    v_isShared_4218_ = v_isSharedCheck_4222_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4215_);
                                    leanh::lean_dec(v___x_4155_);
                                    v___x_4217_ = leanh::lean_box(0);
                                    v_isShared_4218_ = v_isSharedCheck_4222_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4147_ = l_Lean_MessageData_nil;
                v___x_4148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4148_, 0, v___x_4147_);
                return v___x_4148_;
            }
            2 => {
                v___x_4163_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__1,
                );
                leanh::lean_inc_ref(v___x_4157_);
                v___x_4164_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4164_, 0, v___x_4163_);
                leanh::lean_ctor_set(v___x_4164_, 1, v___x_4157_);
                v___x_4165_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__3,
                );
                v___x_4166_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4166_, 0, v___x_4164_);
                leanh::lean_ctor_set(v___x_4166_, 1, v___x_4165_);
                v___x_4167_ = l_Lean_stringToMessageData(v_expected_4140_);
                leanh::lean_inc_ref(v___x_4167_);
                v___x_4168_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4168_, 0, v___x_4166_);
                leanh::lean_ctor_set(v___x_4168_, 1, v___x_4167_);
                v___x_4169_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__5,
                );
                v___x_4170_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4170_, 0, v___x_4168_);
                leanh::lean_ctor_set(v___x_4170_, 1, v___x_4169_);
                v___x_4171_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4171_, 0, v___x_4170_);
                leanh::lean_ctor_set(v___x_4171_, 1, v___x_4167_);
                v___x_4172_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__7,
                );
                v___x_4173_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4173_, 0, v___x_4171_);
                leanh::lean_ctor_set(v___x_4173_, 1, v___x_4172_);
                v___x_4181_ = leanh::lean_box(0);
                v___x_4182_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__1(v___x_4181_, v_a_4159_);
                leanh::lean_dec(v_a_4159_);
                if leanh::lean_obj_tag(v___x_4182_) == 0 {
                    leanh::lean_dec_ref(v___x_4157_);
                    v___x_4183_ = l_Lean_MessageData_nil;
                    v___y_4175_ = v___x_4183_;
                    state = 3;
                    continue;
                } else {
                    v_tail_4184_ = leanh::lean_ctor_get(v___x_4182_, 1);
                    leanh::lean_inc(v_tail_4184_);
                    if leanh::lean_obj_tag(v_tail_4184_) == 0 {
                        v_head_4185_ = leanh::lean_ctor_get(v___x_4182_, 0);
                        v_isSharedCheck_4202_ =
                            (!leanh::lean_is_exclusive(v___x_4182_)) as u8;
                        if v_isSharedCheck_4202_ == 0 {
                            v_unused_4203_ = leanh::lean_ctor_get(v___x_4182_, 1);
                            leanh::lean_dec(v_unused_4203_);
                            v___x_4187_ = v___x_4182_;
                            v_isShared_4188_ = v_isSharedCheck_4202_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_4185_);
                            leanh::lean_dec(v___x_4182_);
                            v___x_4187_ = leanh::lean_box(0);
                            v_isShared_4188_ = v_isSharedCheck_4202_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tail_4184_);
                        v___x_4204_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once
                            ),
                            _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8,
                        );
                        v___x_4205_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16_once
                            ),
                            _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__16,
                        );
                        v___x_4206_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4206_, 0, v___x_4205_);
                        leanh::lean_ctor_set(v___x_4206_, 1, v___x_4157_);
                        v___x_4207_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18_once
                            ),
                            _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__18,
                        );
                        v___x_4208_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4208_, 0, v___x_4206_);
                        leanh::lean_ctor_set(v___x_4208_, 1, v___x_4207_);
                        v___x_4209_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4209_, 0, v___x_4204_);
                        leanh::lean_ctor_set(v___x_4209_, 1, v___x_4208_);
                        v___x_4210_ = l_List_mapTR_loop___at___00Lean_Elab_Term_hintAutoImplicitFailure_spec__2(v___x_4182_, v___x_4181_);
                        v___x_4211_ = l_Lean_MessageData_nil;
                        v___x_4212_ = l_Lean_MessageData_joinSep(v___x_4210_, v___x_4211_);
                        v___x_4213_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4213_, 0, v___x_4209_);
                        leanh::lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                        v___y_4175_ = v___x_4213_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4176_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4176_, 0, v___x_4173_);
                leanh::lean_ctor_set(v___x_4176_, 1, v___y_4175_);
                v___x_4177_ = l_Lean_MessageData_hint_x27(v___x_4176_);
                if v_isShared_4162_ == 0 {
                    leanh::lean_ctor_set(v___x_4161_, 0, v___x_4177_);
                    v___x_4179_ = v___x_4161_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
                    v___x_4179_ = v_reuseFailAlloc_4180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4179_;
            }
            5 => {
                v___x_4189_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__8,
                );
                v___x_4190_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__10,
                );
                v___x_4191_ = 0;
                v___x_4192_ = l_Lean_MessageData_ofConstName(v_head_4185_, v___x_4191_);
                if v_isShared_4188_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4187_, 7);
                    leanh::lean_ctor_set(v___x_4187_, 1, v___x_4192_);
                    leanh::lean_ctor_set(v___x_4187_, 0, v___x_4190_);
                    v___x_4194_ = v___x_4187_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 1, v___x_4192_);
                    v___x_4194_ = v_reuseFailAlloc_4201_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4195_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__12,
                );
                v___x_4196_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4196_, 0, v___x_4194_);
                leanh::lean_ctor_set(v___x_4196_, 1, v___x_4195_);
                v___x_4197_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4197_, 0, v___x_4196_);
                leanh::lean_ctor_set(v___x_4197_, 1, v___x_4157_);
                v___x_4198_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14_once
                    ),
                    _init_l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___closed__14,
                );
                v___x_4199_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4199_, 0, v___x_4197_);
                leanh::lean_ctor_set(v___x_4199_, 1, v___x_4198_);
                v___x_4200_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4200_, 0, v___x_4189_);
                leanh::lean_ctor_set(v___x_4200_, 1, v___x_4199_);
                v___y_4175_ = v___x_4200_;
                state = 3;
                continue;
            }
            7 => {
                if v_isShared_4218_ == 0 {
                    v___x_4220_ = v___x_4217_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4221_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
                    v___x_4220_ = v_reuseFailAlloc_4221_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_hintAutoImplicitFailure___redArg___boxed(
    mut v_exp_4223_: *mut leanh::LeanObject,
    mut v_expected_4224_: *mut leanh::LeanObject,
    mut v_a_4225_: *mut leanh::LeanObject,
    mut v_a_4226_: *mut leanh::LeanObject,
    mut v_a_4227_: *mut leanh::LeanObject,
    mut v_a_4228_: *mut leanh::LeanObject,
    mut v_a_4229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4230_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(
        v_exp_4223_,
        v_expected_4224_,
        v_a_4225_,
        v_a_4226_,
        v_a_4227_,
        v_a_4228_,
    );
    leanh::lean_dec(v_a_4228_);
    leanh::lean_dec_ref(v_a_4227_);
    leanh::lean_dec_ref(v_a_4226_);
    leanh::lean_dec_ref(v_a_4225_);
    leanh::lean_dec_ref(v_exp_4223_);
    return v_res_4230_;
}
pub unsafe fn l_Lean_Elab_Term_hintAutoImplicitFailure(
    mut v_exp_4231_: *mut leanh::LeanObject,
    mut v_expected_4232_: *mut leanh::LeanObject,
    mut v_a_4233_: *mut leanh::LeanObject,
    mut v_a_4234_: *mut leanh::LeanObject,
    mut v_a_4235_: *mut leanh::LeanObject,
    mut v_a_4236_: *mut leanh::LeanObject,
    mut v_a_4237_: *mut leanh::LeanObject,
    mut v_a_4238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4240_ = l_Lean_Elab_Term_hintAutoImplicitFailure___redArg(
        v_exp_4231_,
        v_expected_4232_,
        v_a_4233_,
        v_a_4235_,
        v_a_4237_,
        v_a_4238_,
    );
    return v___x_4240_;
}
pub unsafe fn l_Lean_Elab_Term_hintAutoImplicitFailure___boxed(
    mut v_exp_4241_: *mut leanh::LeanObject,
    mut v_expected_4242_: *mut leanh::LeanObject,
    mut v_a_4243_: *mut leanh::LeanObject,
    mut v_a_4244_: *mut leanh::LeanObject,
    mut v_a_4245_: *mut leanh::LeanObject,
    mut v_a_4246_: *mut leanh::LeanObject,
    mut v_a_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
    mut v_a_4249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4250_ = l_Lean_Elab_Term_hintAutoImplicitFailure(
        v_exp_4241_,
        v_expected_4242_,
        v_a_4243_,
        v_a_4244_,
        v_a_4245_,
        v_a_4246_,
        v_a_4247_,
        v_a_4248_,
    );
    leanh::lean_dec(v_a_4248_);
    leanh::lean_dec_ref(v_a_4247_);
    leanh::lean_dec(v_a_4246_);
    leanh::lean_dec_ref(v_a_4245_);
    leanh::lean_dec(v_a_4244_);
    leanh::lean_dec_ref(v_a_4243_);
    leanh::lean_dec_ref(v_exp_4241_);
    return v_res_4250_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_IdentifierSuggestion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_DeclModifiers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_IdentifierSuggestion_0__Lean_initFn_00___x40_Lean_IdentifierSuggestion_3030853032____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_IdentifierSuggestion_0__Lean_identifierSuggestionsImpl,
    );
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_IdentifierSuggestion(
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
pub unsafe fn initialize_Lean_IdentifierSuggestion(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_DeclModifiers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ErrorUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_IdentifierSuggestion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_IdentifierSuggestion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_IdentifierSuggestion(builtin);
}