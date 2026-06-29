// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Metavariable
// Imports: Lean.PrettyPrinter.Delaborator.Basic Lean.Elab.ErrorUtils
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_replacePrefix, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_Name_num___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node2, l_Lean_addMacroScope,
    l_Lean_reservedMacroScope, l_List_lengthTR___redArg, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Elab::ErrorUtils::{
    initialize_Lean_Elab_ErrorUtils, runtime_initialize_Lean_Elab_ErrorUtils,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_consumeMData,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn_x27, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isMVar, l_Lean_Expr_sort___override, l_Lean_instBEqFVarId_beq,
    l_Lean_instBEqMVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_contains, l_Lean_LocalContext_isSubPrefixOf, l_Lean_LocalDecl_fvarId,
    l_Lean_LocalDecl_hasValue, l_Lean_LocalDecl_index, l_Lean_LocalDecl_userName,
    lean_local_ctx_find,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_MVarId_findDecl_x3f___redArg, l_Lean_MVarId_getDecl, l_Lean_PPContext_runMetaM___redArg,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVarsNoDelayed;
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_findUserName_x3f, l_Lean_MetavarContext_getDecl,
    l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f,
    l_Lean_MetavarContext_getExprAssignmentCore_x3f, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::{
    initialize_Lean_PrettyPrinter_Delaborator_Basic,
    l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Options::{
    l_Lean_getPPMVars, l_Lean_getPPMVars___boxed, l_Lean_getPPMVarsAnonymous,
    l_Lean_getPPMVarsAnonymous___boxed,
};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [109, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value) as *mut crate::leanh::LeanObject,9694982152043229093 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 117, 110, 105, 113, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value) as *mut crate::leanh::LeanObject,3978731030111751661 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 109, 118, 97, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11782265356766657952 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value:
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
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value:
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
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_1:
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
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_2:
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
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value:
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
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        11921244625177918938 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5_value:
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
    m_data: [63, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6_value:
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
    m_data: [95, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value:
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
    m_data: [95, 100, 101, 108, 97, 98, 77, 86, 97, 114, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        16016571949189376859 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value:
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
    m_fun: l_Lean_getPPMVars___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value:
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
    m_fun: l_Lean_getPPMVarsAnonymous___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value:
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
    m_fun: l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value:
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
    m_fun: l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [32, 40, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 41, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [63, 95, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [10, 10, 65, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [32, 105, 110, 32, 116, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 39, 115, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 58, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [10, 10, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [86, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [86, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [32, 97, 98, 115, 101, 110, 116, 32, 102, 114, 111, 109, 32, 116, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 39, 115, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 58, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0_value: crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [32, 83, 117, 98, 115, 116, 105, 116, 117, 116, 105, 111, 110, 32, 105, 115, 32, 97, 119, 97, 105, 116, 105, 110, 103, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0_value: crate::leanh::LeanStringObject<225> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 225, m_capacity: 225, m_length: 224, m_data: [83, 117, 98, 115, 116, 105, 116, 117, 116, 105, 111, 110, 32, 105, 115, 32, 100, 101, 108, 97, 121, 101, 100, 32, 117, 110, 116, 105, 108, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 39, 115, 32, 118, 97, 108, 117, 101, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 110, 111, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 44, 32, 115, 105, 110, 99, 101, 32, 97, 108, 108, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 32, 111, 102, 32, 116, 104, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 102, 114, 111, 109, 32, 105, 116, 115, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 119, 105, 108, 108, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 118, 97, 108, 105, 100, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 99, 111, 110, 116, 101, 120, 116, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value: crate::leanh::LeanStringObject<89> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [80, 97, 114, 116, 32, 111, 102, 32, 116, 104, 101, 32, 101, 110, 99, 111, 100, 105, 110, 103, 32, 111, 102, 32, 116, 104, 101, 32, 42, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 42, 32, 109, 101, 99, 104, 97, 110, 105, 115, 109, 46, 32, 82, 101, 112, 114, 101, 115, 101, 110, 116, 115, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [44, 32, 119, 104, 105, 99, 104, 32, 104, 97, 115, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value: crate::leanh::LeanStringObject<125> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 125, m_capacity: 125, m_length: 124, m_data: [91, 69, 114, 114, 111, 114, 58, 32, 84, 104, 105, 115, 32, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 32, 114, 101, 102, 101, 114, 115, 32, 116, 111, 32, 97, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 111, 110, 116, 101, 120, 116, 46, 32, 80, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 116, 104, 105, 115, 32, 105, 115, 115, 117, 101, 46, 93, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 97, 115, 115, 105, 103, 110, 101, 100, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value: crate::leanh::LeanStringObject<88> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 88, m_capacity: 88, m_length: 87, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 97, 115, 115, 105, 103, 110, 101, 100, 44, 32, 98, 117, 116, 32, 105, 116, 32, 97, 112, 112, 101, 97, 114, 115, 32, 104, 101, 114, 101, 32, 118, 105, 97, 32, 97, 32, 42, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 42, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value: crate::leanh::LeanStringObject<86> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 97, 115, 115, 105, 103, 110, 101, 100, 32, 100, 117, 101, 32, 116, 111, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 111, 110, 116, 101, 120, 116, 32, 100, 101, 112, 116, 104, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 115, 32, 104, 101, 114, 101, 32, 118, 105, 97, 32, 97, 32, 42, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 42, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 97, 115, 32, 97, 32, 110, 97, 109, 101, 32, 98, 117, 116, 32, 105, 116, 32, 105, 115, 32, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9_value: crate::leanh::LeanStringObject<221> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 221, m_capacity: 221, m_length: 220, m_data: [65, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 105, 110, 103, 32, 97, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 116, 104, 97, 116, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 115, 111, 108, 118, 101, 100, 32, 102, 111, 114, 32, 98, 121, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 100, 117, 114, 105, 110, 103, 32, 116, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 115, 115, 46, 32, 84, 104, 101, 121, 32, 97, 114, 101, 32, 99, 114, 101, 97, 116, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 97, 115, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 115, 32, 102, 111, 114, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 97, 110, 100, 32, 98, 121, 32, 96, 95, 96, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 32, 115, 121, 110, 116, 97, 120, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10_value: crate::leanh::LeanStringObject<240> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 240, m_capacity: 240, m_length: 239, m_data: [65, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 105, 110, 103, 32, 97, 32, 116, 121, 112, 101, 99, 108, 97, 115, 115, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 119, 104, 111, 115, 101, 32, 115, 121, 110, 116, 104, 101, 115, 105, 115, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 112, 101, 110, 100, 105, 110, 103, 46, 32, 84, 104, 101, 121, 32, 99, 97, 110, 32, 98, 101, 32, 115, 111, 108, 118, 101, 100, 32, 102, 111, 114, 32, 98, 121, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 100, 117, 114, 105, 110, 103, 32, 116, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 115, 115, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 105, 110, 102, 101, 114, 114, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 97, 110, 100, 32, 116, 104, 101, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 109, 117, 115, 116, 32, 98, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11_value: crate::leanh::LeanStringObject<235> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 235, m_capacity: 235, m_length: 234, m_data: [65, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 105, 110, 103, 32, 97, 32, 116, 97, 99, 116, 105, 99, 32, 103, 111, 97, 108, 32, 111, 114, 32, 97, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 119, 104, 111, 115, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 112, 101, 110, 100, 105, 110, 103, 46, 32, 84, 104, 101, 121, 32, 117, 115, 117, 97, 108, 108, 121, 32, 97, 99, 116, 32, 108, 105, 107, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 117, 110, 116, 105, 108, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 99, 111, 109, 112, 108, 101, 116, 101, 108, 121, 32, 115, 111, 108, 118, 101, 100, 32, 102, 111, 114, 46, 32, 84, 104, 101, 121, 32, 99, 97, 110, 32, 98, 101, 32, 99, 114, 101, 97, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 96, 63, 95, 96, 32, 97, 110, 100, 32, 96, 63, 110, 96, 32, 115, 121, 110, 116, 104, 101, 116, 105, 99, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 32, 115, 121, 110, 116, 97, 120, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12_value: crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [91, 69, 114, 114, 111, 114, 58, 32, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 111, 110, 116, 101, 120, 116, 46, 32, 80, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 116, 104, 105, 115, 32, 105, 115, 115, 117, 101, 46, 93, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(
    mut v_x_1751_: *mut crate::leanh::LeanObject,
    mut v_x_1752_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1751_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1752_) == 0 {
            let mut v___x_1753_: u8 = 0;
            v___x_1753_ = 1;
            return v___x_1753_;
        } else {
            let mut v___x_1754_: u8 = 0;
            v___x_1754_ = 0;
            return v___x_1754_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1752_) == 0 {
            let mut v___x_1755_: u8 = 0;
            v___x_1755_ = 0;
            return v___x_1755_;
        } else {
            let mut v_val_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1758_: u8 = 0;
            v_val_1756_ = crate::leanh::lean_ctor_get(v_x_1751_, 0);
            v_val_1757_ = crate::leanh::lean_ctor_get(v_x_1752_, 0);
            v___x_1758_ = l_Lean_instBEqMVarId_beq(v_val_1756_, v_val_1757_);
            return v___x_1758_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0___boxed(
    mut v_x_1759_: *mut crate::leanh::LeanObject,
    mut v_x_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1761_: u8 = 0;
    let mut v_r_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1761_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v_x_1759_, v_x_1760_);
    crate::leanh::lean_dec(v_x_1760_);
    crate::leanh::lean_dec(v_x_1759_);
    v_r_1762_ = crate::leanh::lean_box((v_res_1761_) as usize);
    return v_r_1762_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(
    mut v_m_1772_: *mut crate::leanh::LeanObject,
    mut v_mkMVarPlaceholder_1773_: *mut crate::leanh::LeanObject,
    mut v_mkMVar_1774_: *mut crate::leanh::LeanObject,
    mut v_mkMVarDead_1775_: *mut crate::leanh::LeanObject,
    mut v_ppMVars_1776_: u8,
    mut v_ppMVarsAnonymous_1777_: u8,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v_userName_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1807_: u8 = 0;
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_ppMVars_1776_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkMVarDead_1775_);
                    crate::leanh::lean_dec_ref(v_mkMVar_1774_);
                    crate::leanh::lean_dec(v_m_1772_);
                    crate::leanh::lean_inc(v_a_1781_);
                    crate::leanh::lean_inc_ref(v_a_1780_);
                    crate::leanh::lean_inc(v_a_1779_);
                    crate::leanh::lean_inc_ref(v_a_1778_);
                    v___x_1783_ = crate::leanh::lean_apply_5(
                        v_mkMVarPlaceholder_1773_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1783_;
                } else {
                    v___x_1784_ = l_Lean_MVarId_findDecl_x3f___redArg(v_m_1772_, v_a_1779_);
                    if crate::leanh::lean_obj_tag(v___x_1784_) == 0 {
                        v_a_1785_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                        crate::leanh::lean_inc(v_a_1785_);
                        crate::leanh::lean_dec_ref_known(v___x_1784_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1785_) == 1 {
                            v_val_1786_ = crate::leanh::lean_ctor_get(v_a_1785_, 0);
                            v_isSharedCheck_1807_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1785_)) as u8;
                            if v_isSharedCheck_1807_ == 0 {
                                v___x_1788_ = v_a_1785_;
                                v_isShared_1789_ = v_isSharedCheck_1807_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1786_);
                                crate::leanh::lean_dec(v_a_1785_);
                                v___x_1788_ = crate::leanh::lean_box(0);
                                v_isShared_1789_ = v_isSharedCheck_1807_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1785_);
                            crate::leanh::lean_dec_ref(v_mkMVarDead_1775_);
                            crate::leanh::lean_dec_ref(v_mkMVarPlaceholder_1773_);
                            v___x_1808_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3;
                            v___x_1809_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5;
                            v___x_1810_ =
                                l_Lean_Name_replacePrefix(v_m_1772_, v___x_1808_, v___x_1809_);
                            crate::leanh::lean_inc(v_a_1781_);
                            crate::leanh::lean_inc_ref(v_a_1780_);
                            crate::leanh::lean_inc(v_a_1779_);
                            crate::leanh::lean_inc_ref(v_a_1778_);
                            v___x_1811_ = crate::leanh::lean_apply_6(
                                v_mkMVar_1774_,
                                v___x_1810_,
                                v_a_1778_,
                                v_a_1779_,
                                v_a_1780_,
                                v_a_1781_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_1811_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mkMVarDead_1775_);
                        crate::leanh::lean_dec_ref(v_mkMVar_1774_);
                        crate::leanh::lean_dec_ref(v_mkMVarPlaceholder_1773_);
                        crate::leanh::lean_dec(v_m_1772_);
                        v_a_1812_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                        v_isSharedCheck_1819_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1819_ == 0 {
                            v___x_1814_ = v___x_1784_;
                            v_isShared_1815_ = v_isSharedCheck_1819_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1812_);
                            crate::leanh::lean_dec(v___x_1784_);
                            v___x_1814_ = crate::leanh::lean_box(0);
                            v_isShared_1815_ = v_isSharedCheck_1819_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_userName_1790_ = crate::leanh::lean_ctor_get(v_val_1786_, 0);
                if crate::leanh::lean_obj_tag(v_userName_1790_) == 0 {
                    crate::leanh::lean_del_object(v___x_1788_);
                    crate::leanh::lean_dec_ref(v_mkMVarDead_1775_);
                    crate::leanh::lean_dec(v_m_1772_);
                    if v_ppMVarsAnonymous_1777_ == 0 {
                        crate::leanh::lean_dec(v_val_1786_);
                        crate::leanh::lean_dec_ref(v_mkMVar_1774_);
                        crate::leanh::lean_inc(v_a_1781_);
                        crate::leanh::lean_inc_ref(v_a_1780_);
                        crate::leanh::lean_inc(v_a_1779_);
                        crate::leanh::lean_inc_ref(v_a_1778_);
                        v___x_1791_ = crate::leanh::lean_apply_5(
                            v_mkMVarPlaceholder_1773_,
                            v_a_1778_,
                            v_a_1779_,
                            v_a_1780_,
                            v_a_1781_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_1791_;
                    } else {
                        crate::leanh::lean_dec_ref(v_mkMVarPlaceholder_1773_);
                        v_index_1792_ = crate::leanh::lean_ctor_get(v_val_1786_, 6);
                        crate::leanh::lean_inc(v_index_1792_);
                        crate::leanh::lean_dec(v_val_1786_);
                        v___x_1793_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1;
                        v___x_1794_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1795_ = lean_nat_add(v_index_1792_, v___x_1794_);
                        crate::leanh::lean_dec(v_index_1792_);
                        v___x_1796_ = l_Lean_Name_num___override(v___x_1793_, v___x_1795_);
                        crate::leanh::lean_inc(v_a_1781_);
                        crate::leanh::lean_inc_ref(v_a_1780_);
                        crate::leanh::lean_inc(v_a_1779_);
                        crate::leanh::lean_inc_ref(v_a_1778_);
                        v___x_1797_ = crate::leanh::lean_apply_6(
                            v_mkMVar_1774_,
                            v___x_1796_,
                            v_a_1778_,
                            v_a_1779_,
                            v_a_1780_,
                            v_a_1781_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_1797_;
                    }
                } else {
                    crate::leanh::lean_inc(v_userName_1790_);
                    crate::leanh::lean_dec(v_val_1786_);
                    crate::leanh::lean_dec_ref(v_mkMVarPlaceholder_1773_);
                    v___x_1798_ = lean_st_ref_get(v_a_1779_);
                    v_mctx_1799_ = crate::leanh::lean_ctor_get(v___x_1798_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1799_);
                    crate::leanh::lean_dec(v___x_1798_);
                    if v_isShared_1789_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1788_, 0, v_m_1772_);
                        v___x_1801_ = v___x_1788_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_m_1772_);
                        v___x_1801_ = v_reuseFailAlloc_1806_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1802_ =
                    l_Lean_MetavarContext_findUserName_x3f(v_mctx_1799_, v_userName_1790_);
                crate::leanh::lean_dec_ref(v_mctx_1799_);
                v___x_1803_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_1801_, v___x_1802_);
                crate::leanh::lean_dec(v___x_1802_);
                crate::leanh::lean_dec_ref(v___x_1801_);
                if v___x_1803_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkMVar_1774_);
                    crate::leanh::lean_inc(v_a_1781_);
                    crate::leanh::lean_inc_ref(v_a_1780_);
                    crate::leanh::lean_inc(v_a_1779_);
                    crate::leanh::lean_inc_ref(v_a_1778_);
                    v___x_1804_ = crate::leanh::lean_apply_6(
                        v_mkMVarDead_1775_,
                        v_userName_1790_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1804_;
                } else {
                    crate::leanh::lean_dec_ref(v_mkMVarDead_1775_);
                    crate::leanh::lean_inc(v_a_1781_);
                    crate::leanh::lean_inc_ref(v_a_1780_);
                    crate::leanh::lean_inc(v_a_1779_);
                    crate::leanh::lean_inc_ref(v_a_1778_);
                    v___x_1805_ = crate::leanh::lean_apply_6(
                        v_mkMVar_1774_,
                        v_userName_1790_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1805_;
                }
            }
            3 => {
                if v_isShared_1815_ == 0 {
                    v___x_1817_ = v___x_1814_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
                    v___x_1817_ = v_reuseFailAlloc_1818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___boxed(
    mut v_m_1820_: *mut crate::leanh::LeanObject,
    mut v_mkMVarPlaceholder_1821_: *mut crate::leanh::LeanObject,
    mut v_mkMVar_1822_: *mut crate::leanh::LeanObject,
    mut v_mkMVarDead_1823_: *mut crate::leanh::LeanObject,
    mut v_ppMVars_1824_: *mut crate::leanh::LeanObject,
    mut v_ppMVarsAnonymous_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ppMVars_boxed_1831_: u8 = 0;
    let mut v_ppMVarsAnonymous_boxed_1832_: u8 = 0;
    let mut v_res_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ppMVars_boxed_1831_ = (crate::leanh::lean_unbox(v_ppMVars_1824_) as u8);
    v_ppMVarsAnonymous_boxed_1832_ = (crate::leanh::lean_unbox(v_ppMVarsAnonymous_1825_) as u8);
    v_res_1833_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_1820_, v_mkMVarPlaceholder_1821_, v_mkMVar_1822_, v_mkMVarDead_1823_, v_ppMVars_boxed_1831_, v_ppMVarsAnonymous_boxed_1832_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
    crate::leanh::lean_dec(v_a_1829_);
    crate::leanh::lean_dec_ref(v_a_1828_);
    crate::leanh::lean_dec(v_a_1827_);
    crate::leanh::lean_dec_ref(v_a_1826_);
    return v_res_1833_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux(
    mut v_00_u03b1_1834_: *mut crate::leanh::LeanObject,
    mut v_m_1835_: *mut crate::leanh::LeanObject,
    mut v_mkMVarPlaceholder_1836_: *mut crate::leanh::LeanObject,
    mut v_mkMVar_1837_: *mut crate::leanh::LeanObject,
    mut v_mkMVarDead_1838_: *mut crate::leanh::LeanObject,
    mut v_ppMVars_1839_: u8,
    mut v_ppMVarsAnonymous_1840_: u8,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
    mut v_a_1842_: *mut crate::leanh::LeanObject,
    mut v_a_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1846_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_1835_, v_mkMVarPlaceholder_1836_, v_mkMVar_1837_, v_mkMVarDead_1838_, v_ppMVars_1839_, v_ppMVarsAnonymous_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
    return v___x_1846_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___boxed(
    mut v_00_u03b1_1847_: *mut crate::leanh::LeanObject,
    mut v_m_1848_: *mut crate::leanh::LeanObject,
    mut v_mkMVarPlaceholder_1849_: *mut crate::leanh::LeanObject,
    mut v_mkMVar_1850_: *mut crate::leanh::LeanObject,
    mut v_mkMVarDead_1851_: *mut crate::leanh::LeanObject,
    mut v_ppMVars_1852_: *mut crate::leanh::LeanObject,
    mut v_ppMVarsAnonymous_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ppMVars_boxed_1859_: u8 = 0;
    let mut v_ppMVarsAnonymous_boxed_1860_: u8 = 0;
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ppMVars_boxed_1859_ = (crate::leanh::lean_unbox(v_ppMVars_1852_) as u8);
    v_ppMVarsAnonymous_boxed_1860_ = (crate::leanh::lean_unbox(v_ppMVarsAnonymous_1853_) as u8);
    v_res_1861_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux(v_00_u03b1_1847_, v_m_1848_, v_mkMVarPlaceholder_1849_, v_mkMVar_1850_, v_mkMVarDead_1851_, v_ppMVars_boxed_1859_, v_ppMVarsAnonymous_boxed_1860_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
    crate::leanh::lean_dec(v_a_1857_);
    crate::leanh::lean_dec_ref(v_a_1856_);
    crate::leanh::lean_dec(v_a_1855_);
    crate::leanh::lean_dec_ref(v_a_1854_);
    return v_res_1861_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0(
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1867_ = crate::leanh::lean_ctor_get(v___y_1864_, 5);
    v___x_1868_ = 0;
    v___x_1869_ = l_Lean_SourceInfo_fromRef(v_ref_1867_, v___x_1868_);
    v___x_1870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1870_, 0, v___x_1869_);
    return v___x_1870_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed(
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0(
        v___y_1871_,
        v___y_1872_,
        v___y_1873_,
        v___y_1874_,
    );
    crate::leanh::lean_dec(v___y_1874_);
    crate::leanh::lean_dec_ref(v___y_1873_);
    crate::leanh::lean_dec(v___y_1872_);
    crate::leanh::lean_dec_ref(v___y_1871_);
    return v_res_1876_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1(
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1893_ = crate::leanh::lean_ctor_get(v___y_1890_, 5);
    v___x_1894_ = 0;
    v___x_1895_ = l_Lean_SourceInfo_fromRef(v_ref_1893_, v___x_1894_);
    v___x_1896_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4;
    v___x_1897_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
    crate::leanh::lean_inc_n(v___x_1895_, 2);
    v___x_1898_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1895_);
    crate::leanh::lean_ctor_set(v___x_1898_, 1, v___x_1897_);
    v___x_1899_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6;
    v___x_1900_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1895_);
    crate::leanh::lean_ctor_set(v___x_1900_, 1, v___x_1899_);
    v___x_1901_ = l_Lean_Syntax_node2(v___x_1895_, v___x_1896_, v___x_1898_, v___x_1900_);
    v___x_1902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1902_, 0, v___x_1901_);
    return v___x_1902_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed(
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1(
        v___y_1903_,
        v___y_1904_,
        v___y_1905_,
        v___y_1906_,
    );
    crate::leanh::lean_dec(v___y_1906_);
    crate::leanh::lean_dec_ref(v___y_1905_);
    crate::leanh::lean_dec(v___y_1904_);
    crate::leanh::lean_dec_ref(v___y_1903_);
    return v_res_1908_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2(
    mut v___f_1909_: *mut crate::leanh::LeanObject,
    mut v_n_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut v_a_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1914_);
                crate::leanh::lean_inc_ref(v___y_1913_);
                crate::leanh::lean_inc(v___y_1912_);
                crate::leanh::lean_inc_ref(v___y_1911_);
                v___x_1916_ = crate::leanh::lean_apply_5(
                    v___f_1909_,
                    v___y_1911_,
                    v___y_1912_,
                    v___y_1913_,
                    v___y_1914_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1916_) == 0 {
                    v_a_1917_ = crate::leanh::lean_ctor_get(v___x_1916_, 0);
                    v_isSharedCheck_1929_ = (!crate::leanh::lean_is_exclusive(v___x_1916_)) as u8;
                    if v_isSharedCheck_1929_ == 0 {
                        v___x_1919_ = v___x_1916_;
                        v_isShared_1920_ = v_isSharedCheck_1929_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1917_);
                        crate::leanh::lean_dec(v___x_1916_);
                        v___x_1919_ = crate::leanh::lean_box(0);
                        v_isShared_1920_ = v_isSharedCheck_1929_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_n_1910_);
                    v_a_1930_ = crate::leanh::lean_ctor_get(v___x_1916_, 0);
                    v_isSharedCheck_1937_ = (!crate::leanh::lean_is_exclusive(v___x_1916_)) as u8;
                    if v_isSharedCheck_1937_ == 0 {
                        v___x_1932_ = v___x_1916_;
                        v_isShared_1933_ = v_isSharedCheck_1937_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1930_);
                        crate::leanh::lean_dec(v___x_1916_);
                        v___x_1932_ = crate::leanh::lean_box(0);
                        v_isShared_1933_ = v_isSharedCheck_1937_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1921_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4;
                v___x_1922_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
                crate::leanh::lean_inc(v_a_1917_);
                v___x_1923_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1923_, 0, v_a_1917_);
                crate::leanh::lean_ctor_set(v___x_1923_, 1, v___x_1922_);
                v___x_1924_ = lean_mk_syntax_ident(v_n_1910_);
                v___x_1925_ = l_Lean_Syntax_node2(v_a_1917_, v___x_1921_, v___x_1923_, v___x_1924_);
                if v_isShared_1920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1919_, 0, v___x_1925_);
                    v___x_1927_ = v___x_1919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
                    v___x_1927_ = v_reuseFailAlloc_1928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1927_;
            }
            3 => {
                if v_isShared_1933_ == 0 {
                    v___x_1935_ = v___x_1932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
                    v___x_1935_ = v_reuseFailAlloc_1936_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2___boxed(
    mut v___f_1938_: *mut crate::leanh::LeanObject,
    mut v_n_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
    mut v___y_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2(
        v___f_1938_,
        v_n_1939_,
        v___y_1940_,
        v___y_1941_,
        v___y_1942_,
        v___y_1943_,
    );
    crate::leanh::lean_dec(v___y_1943_);
    crate::leanh::lean_dec_ref(v___y_1942_);
    crate::leanh::lean_dec(v___y_1941_);
    crate::leanh::lean_dec_ref(v___y_1940_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(
    mut v___f_1949_: *mut crate::leanh::LeanObject,
    mut v_m_1950_: *mut crate::leanh::LeanObject,
    mut v_n_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1961_: u8 = 0;
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v_a_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1955_);
                crate::leanh::lean_inc_ref(v___y_1954_);
                crate::leanh::lean_inc(v___y_1953_);
                crate::leanh::lean_inc_ref(v___y_1952_);
                v___x_1957_ = crate::leanh::lean_apply_5(
                    v___f_1949_,
                    v___y_1952_,
                    v___y_1953_,
                    v___y_1954_,
                    v___y_1955_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1957_) == 0 {
                    v_a_1958_ = crate::leanh::lean_ctor_get(v___x_1957_, 0);
                    v_isSharedCheck_1974_ = (!crate::leanh::lean_is_exclusive(v___x_1957_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v___x_1960_ = v___x_1957_;
                        v_isShared_1961_ = v_isSharedCheck_1974_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1958_);
                        crate::leanh::lean_dec(v___x_1957_);
                        v___x_1960_ = crate::leanh::lean_box(0);
                        v_isShared_1961_ = v_isSharedCheck_1974_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_n_1951_);
                    crate::leanh::lean_dec(v_m_1950_);
                    v_a_1975_ = crate::leanh::lean_ctor_get(v___x_1957_, 0);
                    v_isSharedCheck_1982_ = (!crate::leanh::lean_is_exclusive(v___x_1957_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1977_ = v___x_1957_;
                        v_isShared_1978_ = v_isSharedCheck_1982_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1975_);
                        crate::leanh::lean_dec(v___x_1957_);
                        v___x_1977_ = crate::leanh::lean_box(0);
                        v_isShared_1978_ = v_isSharedCheck_1982_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1962_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1;
                v___x_1963_ = l_Lean_Name_append(v___x_1962_, v_m_1950_);
                v___x_1964_ = l_Lean_reservedMacroScope;
                v___x_1965_ = l_Lean_addMacroScope(v___x_1963_, v_n_1951_, v___x_1964_);
                v___x_1966_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4;
                v___x_1967_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
                crate::leanh::lean_inc(v_a_1958_);
                v___x_1968_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1968_, 0, v_a_1958_);
                crate::leanh::lean_ctor_set(v___x_1968_, 1, v___x_1967_);
                v___x_1969_ = lean_mk_syntax_ident(v___x_1965_);
                v___x_1970_ = l_Lean_Syntax_node2(v_a_1958_, v___x_1966_, v___x_1968_, v___x_1969_);
                if v_isShared_1961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1960_, 0, v___x_1970_);
                    v___x_1972_ = v___x_1960_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1972_;
            }
            3 => {
                if v_isShared_1978_ == 0 {
                    v___x_1980_ = v___x_1977_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
                    v___x_1980_ = v_reuseFailAlloc_1981_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed(
    mut v___f_1983_: *mut crate::leanh::LeanObject,
    mut v_m_1984_: *mut crate::leanh::LeanObject,
    mut v_n_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(
        v___f_1983_,
        v_m_1984_,
        v_n_1985_,
        v___y_1986_,
        v___y_1987_,
        v___y_1988_,
        v___y_1989_,
    );
    crate::leanh::lean_dec(v___y_1989_);
    crate::leanh::lean_dec_ref(v___y_1988_);
    crate::leanh::lean_dec(v___y_1987_);
    crate::leanh::lean_dec_ref(v___y_1986_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux(
    mut v_m_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
    mut v_a_2000_: *mut crate::leanh::LeanObject,
    mut v_a_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_a_2004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut v_a_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2006_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0;
                v___x_2007_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(
                    v___x_2006_,
                    v_a_1999_,
                    v_a_2000_,
                    v_a_2001_,
                    v_a_2002_,
                    v_a_2003_,
                    v_a_2004_,
                );
                if crate::leanh::lean_obj_tag(v___x_2007_) == 0 {
                    v_a_2008_ = crate::leanh::lean_ctor_get(v___x_2007_, 0);
                    crate::leanh::lean_inc(v_a_2008_);
                    crate::leanh::lean_dec_ref_known(v___x_2007_, 1);
                    v___x_2009_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1;
                    v___x_2010_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(
                        v___x_2009_,
                        v_a_1999_,
                        v_a_2000_,
                        v_a_2001_,
                        v_a_2002_,
                        v_a_2003_,
                        v_a_2004_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2010_) == 0 {
                        v_a_2011_ = crate::leanh::lean_ctor_get(v___x_2010_, 0);
                        crate::leanh::lean_inc(v_a_2011_);
                        crate::leanh::lean_dec_ref_known(v___x_2010_, 1);
                        v___f_2012_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2;
                        v___f_2013_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3;
                        v___f_2014_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4;
                        crate::leanh::lean_inc(v_m_1998_);
                        v___f_2015_ = crate::leanh::lean_alloc_closure(
                            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed
                                as *mut core::ffi::c_void,
                            8,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_2015_, 0, v___f_2012_);
                        crate::leanh::lean_closure_set(v___f_2015_, 1, v_m_1998_);
                        v___x_2016_ = (crate::leanh::lean_unbox(v_a_2008_) as u8);
                        crate::leanh::lean_dec(v_a_2008_);
                        v___x_2017_ = (crate::leanh::lean_unbox(v_a_2011_) as u8);
                        crate::leanh::lean_dec(v_a_2011_);
                        v___x_2018_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_1998_, v___f_2013_, v___f_2014_, v___f_2015_, v___x_2016_, v___x_2017_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
                        return v___x_2018_;
                    } else {
                        crate::leanh::lean_dec(v_a_2008_);
                        crate::leanh::lean_dec(v_m_1998_);
                        v_a_2019_ = crate::leanh::lean_ctor_get(v___x_2010_, 0);
                        v_isSharedCheck_2026_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2010_)) as u8;
                        if v_isSharedCheck_2026_ == 0 {
                            v___x_2021_ = v___x_2010_;
                            v_isShared_2022_ = v_isSharedCheck_2026_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2019_);
                            crate::leanh::lean_dec(v___x_2010_);
                            v___x_2021_ = crate::leanh::lean_box(0);
                            v_isShared_2022_ = v_isSharedCheck_2026_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_m_1998_);
                    v_a_2027_ = crate::leanh::lean_ctor_get(v___x_2007_, 0);
                    v_isSharedCheck_2034_ = (!crate::leanh::lean_is_exclusive(v___x_2007_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2029_ = v___x_2007_;
                        v_isShared_2030_ = v_isSharedCheck_2034_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2027_);
                        crate::leanh::lean_dec(v___x_2007_);
                        v___x_2029_ = crate::leanh::lean_box(0);
                        v_isShared_2030_ = v_isSharedCheck_2034_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2022_ == 0 {
                    v___x_2024_ = v___x_2021_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2025_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
                    v___x_2024_ = v_reuseFailAlloc_2025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2024_;
            }
            3 => {
                if v_isShared_2030_ == 0 {
                    v___x_2032_ = v___x_2029_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
                    v___x_2032_ = v_reuseFailAlloc_2033_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___boxed(
    mut v_m_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
    mut v_a_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2043_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux(
        v_m_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_,
    );
    crate::leanh::lean_dec(v_a_2041_);
    crate::leanh::lean_dec_ref(v_a_2040_);
    crate::leanh::lean_dec(v_a_2039_);
    crate::leanh::lean_dec_ref(v_a_2038_);
    crate::leanh::lean_dec(v_a_2037_);
    crate::leanh::lean_dec_ref(v_a_2036_);
    return v_res_2043_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0(
    mut v_n_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
    v___x_2052_ = 1;
    v___x_2053_ = l_Lean_Name_toString(v_n_2045_, v___x_2052_);
    v___x_2054_ = lean_string_append(v___x_2051_, v___x_2053_);
    crate::leanh::lean_dec_ref(v___x_2053_);
    v___x_2055_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0;
    v___x_2056_ = lean_string_append(v___x_2054_, v___x_2055_);
    v___x_2057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2057_, 0, v___x_2056_);
    return v___x_2057_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___boxed(
    mut v_n_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
    mut v___y_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0(v_n_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
    crate::leanh::lean_dec(v___y_2062_);
    crate::leanh::lean_dec_ref(v___y_2061_);
    crate::leanh::lean_dec(v___y_2060_);
    crate::leanh::lean_dec_ref(v___y_2059_);
    return v_res_2064_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1(
    mut v_n_2065_: *mut crate::leanh::LeanObject,
    mut v___y_2066_: *mut crate::leanh::LeanObject,
    mut v___y_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
    v___x_2072_ = 1;
    v___x_2073_ = l_Lean_Name_toString(v_n_2065_, v___x_2072_);
    v___x_2074_ = lean_string_append(v___x_2071_, v___x_2073_);
    crate::leanh::lean_dec_ref(v___x_2073_);
    v___x_2075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2075_, 0, v___x_2074_);
    return v___x_2075_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1___boxed(
    mut v_n_2076_: *mut crate::leanh::LeanObject,
    mut v___y_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2082_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1(v_n_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
    crate::leanh::lean_dec(v___y_2080_);
    crate::leanh::lean_dec_ref(v___y_2079_);
    crate::leanh::lean_dec(v___y_2078_);
    crate::leanh::lean_dec_ref(v___y_2077_);
    return v_res_2082_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2(
    mut v___x_2083_: *mut crate::leanh::LeanObject,
    mut v___y_2084_: *mut crate::leanh::LeanObject,
    mut v___y_2085_: *mut crate::leanh::LeanObject,
    mut v___y_2086_: *mut crate::leanh::LeanObject,
    mut v___y_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2089_, 0, v___x_2083_);
    return v___x_2089_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2___boxed(
    mut v___x_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2(v___x_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
    crate::leanh::lean_dec(v___y_2094_);
    crate::leanh::lean_dec_ref(v___y_2093_);
    crate::leanh::lean_dec(v___y_2092_);
    crate::leanh::lean_dec_ref(v___y_2091_);
    return v_res_2096_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(
    mut v_m_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_2108_ = crate::leanh::lean_ctor_get(v_a_2105_, 2);
    v___f_2109_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0;
    v___f_2110_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1;
    v___f_2111_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3;
    v___x_2112_ = l_Lean_getPPMVars(v_options_2108_);
    v___x_2113_ = l_Lean_getPPMVarsAnonymous(v_options_2108_);
    v___x_2114_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_2102_, v___f_2111_, v___f_2110_, v___f_2109_, v___x_2112_, v___x_2113_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
    return v___x_2114_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___boxed(
    mut v_m_2115_: *mut crate::leanh::LeanObject,
    mut v_a_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2121_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_m_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
    crate::leanh::lean_dec(v_a_2119_);
    crate::leanh::lean_dec_ref(v_a_2118_);
    crate::leanh::lean_dec(v_a_2117_);
    crate::leanh::lean_dec_ref(v_a_2116_);
    return v_res_2121_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_x_2123_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2124_: u8 = 0;
    let mut v_key_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2123_) == 0 {
                    v___x_2124_ = 0;
                    return v___x_2124_;
                } else {
                    v_key_2125_ = crate::leanh::lean_ctor_get(v_x_2123_, 0);
                    v_tail_2126_ = crate::leanh::lean_ctor_get(v_x_2123_, 2);
                    v___x_2127_ = l_Lean_instBEqFVarId_beq(v_key_2125_, v_a_2122_);
                    if v___x_2127_ == 0 {
                        v_x_2123_ = v_tail_2126_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2127_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg___boxed(
    mut v_a_2129_: *mut crate::leanh::LeanObject,
    mut v_x_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2131_: u8 = 0;
    let mut v_r_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_2129_, v_x_2130_);
    crate::leanh::lean_dec(v_x_2130_);
    crate::leanh::lean_dec(v_a_2129_);
    v_r_2132_ = crate::leanh::lean_box((v_res_2131_) as usize);
    return v_r_2132_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(
    mut v_m_2133_: *mut crate::leanh::LeanObject,
    mut v_a_2134_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u64 = 0;
    let mut v___x_2138_: u64 = 0;
    let mut v___x_2139_: u64 = 0;
    let mut v_fold_2140_: u64 = 0;
    let mut v___x_2141_: u64 = 0;
    let mut v___x_2142_: u64 = 0;
    let mut v___x_2143_: u64 = 0;
    let mut v___x_2144_: usize = 0;
    let mut v___x_2145_: usize = 0;
    let mut v___x_2146_: usize = 0;
    let mut v___x_2147_: usize = 0;
    let mut v___x_2148_: usize = 0;
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    v_buckets_2135_ = crate::leanh::lean_ctor_get(v_m_2133_, 1);
    v___x_2136_ = lean_array_get_size(v_buckets_2135_);
    v___x_2137_ = l_Lean_instHashableFVarId_hash(v_a_2134_);
    v___x_2138_ = 32u64;
    v___x_2139_ = lean_uint64_shift_right(v___x_2137_, v___x_2138_);
    v_fold_2140_ = lean_uint64_xor(v___x_2137_, v___x_2139_);
    v___x_2141_ = 16u64;
    v___x_2142_ = lean_uint64_shift_right(v_fold_2140_, v___x_2141_);
    v___x_2143_ = lean_uint64_xor(v_fold_2140_, v___x_2142_);
    v___x_2144_ = lean_uint64_to_usize(v___x_2143_);
    v___x_2145_ = lean_usize_of_nat(v___x_2136_);
    v___x_2146_ = 1usize;
    v___x_2147_ = lean_usize_sub(v___x_2145_, v___x_2146_);
    v___x_2148_ = lean_usize_land(v___x_2144_, v___x_2147_);
    v___x_2149_ = lean_array_uget_borrowed(v_buckets_2135_, v___x_2148_);
    v___x_2150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_2134_, v___x_2149_);
    return v___x_2150_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg___boxed(
    mut v_m_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2153_: u8 = 0;
    let mut v_r_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_2151_, v_a_2152_);
    crate::leanh::lean_dec(v_a_2152_);
    crate::leanh::lean_dec_ref(v_m_2151_);
    v_r_2154_ = crate::leanh::lean_box((v_res_2153_) as usize);
    return v_r_2154_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_x_2155_: *mut crate::leanh::LeanObject,
    mut v_x_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u64 = 0;
    let mut v___x_2165_: u64 = 0;
    let mut v___x_2166_: u64 = 0;
    let mut v_fold_2167_: u64 = 0;
    let mut v___x_2168_: u64 = 0;
    let mut v___x_2169_: u64 = 0;
    let mut v___x_2170_: u64 = 0;
    let mut v___x_2171_: usize = 0;
    let mut v___x_2172_: usize = 0;
    let mut v___x_2173_: usize = 0;
    let mut v___x_2174_: usize = 0;
    let mut v___x_2175_: usize = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2156_) == 0 {
                    return v_x_2155_;
                } else {
                    v_key_2157_ = crate::leanh::lean_ctor_get(v_x_2156_, 0);
                    v_value_2158_ = crate::leanh::lean_ctor_get(v_x_2156_, 1);
                    v_tail_2159_ = crate::leanh::lean_ctor_get(v_x_2156_, 2);
                    v_isSharedCheck_2182_ = (!crate::leanh::lean_is_exclusive(v_x_2156_)) as u8;
                    if v_isSharedCheck_2182_ == 0 {
                        v___x_2161_ = v_x_2156_;
                        v_isShared_2162_ = v_isSharedCheck_2182_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2159_);
                        crate::leanh::lean_inc(v_value_2158_);
                        crate::leanh::lean_inc(v_key_2157_);
                        crate::leanh::lean_dec(v_x_2156_);
                        v___x_2161_ = crate::leanh::lean_box(0);
                        v_isShared_2162_ = v_isSharedCheck_2182_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2163_ = lean_array_get_size(v_x_2155_);
                v___x_2164_ = l_Lean_instHashableFVarId_hash(v_key_2157_);
                v___x_2165_ = 32u64;
                v___x_2166_ = lean_uint64_shift_right(v___x_2164_, v___x_2165_);
                v_fold_2167_ = lean_uint64_xor(v___x_2164_, v___x_2166_);
                v___x_2168_ = 16u64;
                v___x_2169_ = lean_uint64_shift_right(v_fold_2167_, v___x_2168_);
                v___x_2170_ = lean_uint64_xor(v_fold_2167_, v___x_2169_);
                v___x_2171_ = lean_uint64_to_usize(v___x_2170_);
                v___x_2172_ = lean_usize_of_nat(v___x_2163_);
                v___x_2173_ = 1usize;
                v___x_2174_ = lean_usize_sub(v___x_2172_, v___x_2173_);
                v___x_2175_ = lean_usize_land(v___x_2171_, v___x_2174_);
                v___x_2176_ = lean_array_uget_borrowed(v_x_2155_, v___x_2175_);
                crate::leanh::lean_inc(v___x_2176_);
                if v_isShared_2162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2161_, 2, v___x_2176_);
                    v___x_2178_ = v___x_2161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_key_2157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_value_2158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2176_);
                    v___x_2178_ = v_reuseFailAlloc_2181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2179_ = lean_array_uset(v_x_2155_, v___x_2175_, v___x_2178_);
                v_x_2155_ = v___x_2179_;
                v_x_2156_ = v_tail_2159_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(
    mut v_i_2183_: *mut crate::leanh::LeanObject,
    mut v_source_2184_: *mut crate::leanh::LeanObject,
    mut v_target_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v_es_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2186_ = lean_array_get_size(v_source_2184_);
                v___x_2187_ = lean_nat_dec_lt(v_i_2183_, v___x_2186_);
                if v___x_2187_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2184_);
                    crate::leanh::lean_dec(v_i_2183_);
                    return v_target_2185_;
                } else {
                    v_es_2188_ = lean_array_fget(v_source_2184_, v_i_2183_);
                    v___x_2189_ = crate::leanh::lean_box(0);
                    v_source_2190_ = lean_array_fset(v_source_2184_, v_i_2183_, v___x_2189_);
                    v_target_2191_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_target_2185_, v_es_2188_);
                    v___x_2192_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2193_ = lean_nat_add(v_i_2183_, v___x_2192_);
                    crate::leanh::lean_dec(v_i_2183_);
                    v_i_2183_ = v___x_2193_;
                    v_source_2184_ = v_source_2190_;
                    v_target_2185_ = v_target_2191_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(
    mut v_data_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = lean_array_get_size(v_data_2195_);
    v___x_2197_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2198_ = lean_nat_mul(v___x_2196_, v___x_2197_);
    v___x_2199_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2200_ = crate::leanh::lean_box(0);
    v___x_2201_ = lean_mk_array(v_nbuckets_2198_, v___x_2200_);
    v___x_2202_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v___x_2199_, v_data_2195_, v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(
    mut v_m_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
    mut v_b_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: u64 = 0;
    let mut v___x_2210_: u64 = 0;
    let mut v___x_2211_: u64 = 0;
    let mut v_fold_2212_: u64 = 0;
    let mut v___x_2213_: u64 = 0;
    let mut v___x_2214_: u64 = 0;
    let mut v___x_2215_: u64 = 0;
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: usize = 0;
    let mut v___x_2218_: usize = 0;
    let mut v___x_2219_: usize = 0;
    let mut v___x_2220_: usize = 0;
    let mut v_bkt_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v_val_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut v_unused_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2206_ = crate::leanh::lean_ctor_get(v_m_2203_, 0);
                v_buckets_2207_ = crate::leanh::lean_ctor_get(v_m_2203_, 1);
                v___x_2208_ = lean_array_get_size(v_buckets_2207_);
                v___x_2209_ = l_Lean_instHashableFVarId_hash(v_a_2204_);
                v___x_2210_ = 32u64;
                v___x_2211_ = lean_uint64_shift_right(v___x_2209_, v___x_2210_);
                v_fold_2212_ = lean_uint64_xor(v___x_2209_, v___x_2211_);
                v___x_2213_ = 16u64;
                v___x_2214_ = lean_uint64_shift_right(v_fold_2212_, v___x_2213_);
                v___x_2215_ = lean_uint64_xor(v_fold_2212_, v___x_2214_);
                v___x_2216_ = lean_uint64_to_usize(v___x_2215_);
                v___x_2217_ = lean_usize_of_nat(v___x_2208_);
                v___x_2218_ = 1usize;
                v___x_2219_ = lean_usize_sub(v___x_2217_, v___x_2218_);
                v___x_2220_ = lean_usize_land(v___x_2216_, v___x_2219_);
                v_bkt_2221_ = lean_array_uget_borrowed(v_buckets_2207_, v___x_2220_);
                v___x_2222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_2204_, v_bkt_2221_);
                if v___x_2222_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2207_);
                    crate::leanh::lean_inc(v_size_2206_);
                    v_isSharedCheck_2243_ = (!crate::leanh::lean_is_exclusive(v_m_2203_)) as u8;
                    if v_isSharedCheck_2243_ == 0 {
                        v_unused_2244_ = crate::leanh::lean_ctor_get(v_m_2203_, 1);
                        crate::leanh::lean_dec(v_unused_2244_);
                        v_unused_2245_ = crate::leanh::lean_ctor_get(v_m_2203_, 0);
                        crate::leanh::lean_dec(v_unused_2245_);
                        v___x_2224_ = v_m_2203_;
                        v_isShared_2225_ = v_isSharedCheck_2243_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2203_);
                        v___x_2224_ = crate::leanh::lean_box(0);
                        v_isShared_2225_ = v_isSharedCheck_2243_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2205_);
                    crate::leanh::lean_dec(v_a_2204_);
                    return v_m_2203_;
                }
            }
            1 => {
                v___x_2226_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2227_ = lean_nat_add(v_size_2206_, v___x_2226_);
                crate::leanh::lean_dec(v_size_2206_);
                crate::leanh::lean_inc(v_bkt_2221_);
                v___x_2228_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2228_, 0, v_a_2204_);
                crate::leanh::lean_ctor_set(v___x_2228_, 1, v_b_2205_);
                crate::leanh::lean_ctor_set(v___x_2228_, 2, v_bkt_2221_);
                v_buckets_x27_2229_ = lean_array_uset(v_buckets_2207_, v___x_2220_, v___x_2228_);
                v___x_2230_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2231_ = lean_nat_mul(v_size_x27_2227_, v___x_2230_);
                v___x_2232_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2233_ = lean_nat_div(v___x_2231_, v___x_2232_);
                crate::leanh::lean_dec(v___x_2231_);
                v___x_2234_ = lean_array_get_size(v_buckets_x27_2229_);
                v___x_2235_ = lean_nat_dec_le(v___x_2233_, v___x_2234_);
                crate::leanh::lean_dec(v___x_2233_);
                if v___x_2235_ == 0 {
                    v_val_2236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_buckets_x27_2229_);
                    if v_isShared_2225_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2224_, 1, v_val_2236_);
                        crate::leanh::lean_ctor_set(v___x_2224_, 0, v_size_x27_2227_);
                        v___x_2238_ = v___x_2224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_size_x27_2227_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_val_2236_);
                        v___x_2238_ = v_reuseFailAlloc_2239_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2225_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2224_, 1, v_buckets_x27_2229_);
                        crate::leanh::lean_ctor_set(v___x_2224_, 0, v_size_x27_2227_);
                        v___x_2241_ = v___x_2224_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_size_x27_2227_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_buckets_x27_2229_);
                        v___x_2241_ = v_reuseFailAlloc_2242_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2238_;
            }
            3 => {
                return v___x_2241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(
    mut v_val_2249_: *mut crate::leanh::LeanObject,
    mut v_as_2250_: *mut crate::leanh::LeanObject,
    mut v_sz_2251_: usize,
    mut v_i_2252_: usize,
    mut v_b_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v_snd_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v_array_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v_lctx_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: u8 = 0;
    let mut v_fvarId_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2337_: u8 = 0;
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2347_: u8 = 0;
    let mut v_unused_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_unused_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2260_ = lean_usize_dec_lt(v_i_2252_, v_sz_2251_);
                if v___x_2260_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_2249_);
                    v___x_2261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v_b_2253_);
                    return v___x_2261_;
                } else {
                    v_snd_2262_ = crate::leanh::lean_ctor_get(v_b_2253_, 1);
                    v_isSharedCheck_2352_ = (!crate::leanh::lean_is_exclusive(v_b_2253_)) as u8;
                    if v_isSharedCheck_2352_ == 0 {
                        v_unused_2353_ = crate::leanh::lean_ctor_get(v_b_2253_, 0);
                        crate::leanh::lean_dec(v_unused_2353_);
                        v___x_2264_ = v_b_2253_;
                        v_isShared_2265_ = v_isSharedCheck_2352_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2262_);
                        crate::leanh::lean_dec(v_b_2253_);
                        v___x_2264_ = crate::leanh::lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2352_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2257_ = 1usize;
                v___x_2258_ = lean_usize_add(v_i_2252_, v___x_2257_);
                v_i_2252_ = v___x_2258_;
                v_b_2253_ = v_a_2256_;
                state = 0;
                continue;
            }
            2 => {
                v_snd_2266_ = crate::leanh::lean_ctor_get(v_snd_2262_, 1);
                v_fst_2267_ = crate::leanh::lean_ctor_get(v_snd_2262_, 0);
                v_isSharedCheck_2351_ = (!crate::leanh::lean_is_exclusive(v_snd_2262_)) as u8;
                if v_isSharedCheck_2351_ == 0 {
                    v___x_2269_ = v_snd_2262_;
                    v_isShared_2270_ = v_isSharedCheck_2351_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2266_);
                    crate::leanh::lean_inc(v_fst_2267_);
                    crate::leanh::lean_dec(v_snd_2262_);
                    v___x_2269_ = crate::leanh::lean_box(0);
                    v_isShared_2270_ = v_isSharedCheck_2351_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_2271_ = crate::leanh::lean_ctor_get(v_snd_2266_, 0);
                v_start_2272_ = crate::leanh::lean_ctor_get(v_snd_2266_, 1);
                v_stop_2273_ = crate::leanh::lean_ctor_get(v_snd_2266_, 2);
                v___x_2274_ = crate::leanh::lean_box(0);
                v___x_2275_ = lean_nat_dec_lt(v_start_2272_, v_stop_2273_);
                if v___x_2275_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_2249_);
                    if v_isShared_2270_ == 0 {
                        v___x_2277_ = v___x_2269_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_fst_2267_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_snd_2266_);
                        v___x_2277_ = v_reuseFailAlloc_2282_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_2273_);
                    crate::leanh::lean_inc(v_start_2272_);
                    crate::leanh::lean_inc_ref(v_array_2271_);
                    v_isSharedCheck_2347_ = (!crate::leanh::lean_is_exclusive(v_snd_2266_)) as u8;
                    if v_isSharedCheck_2347_ == 0 {
                        v_unused_2348_ = crate::leanh::lean_ctor_get(v_snd_2266_, 2);
                        crate::leanh::lean_dec(v_unused_2348_);
                        v_unused_2349_ = crate::leanh::lean_ctor_get(v_snd_2266_, 1);
                        crate::leanh::lean_dec(v_unused_2349_);
                        v_unused_2350_ = crate::leanh::lean_ctor_get(v_snd_2266_, 0);
                        crate::leanh::lean_dec(v_unused_2350_);
                        v___x_2284_ = v_snd_2266_;
                        v_isShared_2285_ = v_isSharedCheck_2347_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_2266_);
                        v___x_2284_ = crate::leanh::lean_box(0);
                        v_isShared_2285_ = v_isSharedCheck_2347_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2277_);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2274_);
                    v___x_2279_ = v___x_2264_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2277_);
                    v___x_2279_ = v_reuseFailAlloc_2281_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2280_, 0, v___x_2279_);
                return v___x_2280_;
            }
            6 => {
                v_lctx_2286_ = crate::leanh::lean_ctor_get(v_val_2249_, 1);
                v___x_2287_ = lean_array_fget(v_array_2271_, v_start_2272_);
                v_a_2288_ = lean_array_uget_borrowed(v_as_2250_, v_i_2252_);
                v___x_2289_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2290_ = lean_nat_add(v_start_2272_, v___x_2289_);
                crate::leanh::lean_dec(v_start_2272_);
                if v_isShared_2285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2284_, 1, v___x_2290_);
                    v___x_2292_ = v___x_2284_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2346_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_array_2271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_stop_2273_);
                    v___x_2292_ = v_reuseFailAlloc_2346_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2293_ = l_Lean_Expr_fvarId_x21(v_a_2288_);
                crate::leanh::lean_inc_ref(v_lctx_2286_);
                v___x_2294_ = lean_local_ctx_find(v_lctx_2286_, v___x_2293_);
                if crate::leanh::lean_obj_tag(v___x_2294_) == 1 {
                    v_val_2295_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2337_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2337_ == 0 {
                        v___x_2297_ = v___x_2294_;
                        v_isShared_2298_ = v_isSharedCheck_2337_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2295_);
                        crate::leanh::lean_dec(v___x_2294_);
                        v___x_2297_ = crate::leanh::lean_box(0);
                        v_isShared_2298_ = v_isSharedCheck_2337_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2294_);
                    crate::leanh::lean_dec(v___x_2287_);
                    crate::leanh::lean_dec_ref(v_val_2249_);
                    v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0;
                    if v_isShared_2270_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                        v___x_2340_ = v___x_2269_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_2345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_fst_2267_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2292_);
                        v___x_2340_ = v_reuseFailAlloc_2345_;
                        state = 19;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2299_ = 0;
                v___x_2300_ = l_Lean_LocalDecl_hasValue(v_val_2295_, v___x_2299_);
                crate::leanh::lean_dec(v_val_2295_);
                if v___x_2300_ == 0 {
                    if crate::leanh::lean_obj_tag(v___x_2287_) == 1 {
                        v_fvarId_2301_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                        crate::leanh::lean_inc(v_fvarId_2301_);
                        crate::leanh::lean_dec_ref_known(v___x_2287_, 1);
                        v___x_2302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_fst_2267_, v_fvarId_2301_);
                        if v___x_2302_ == 0 {
                            crate::leanh::lean_del_object(v___x_2297_);
                            v___x_2303_ = crate::leanh::lean_box(0);
                            v___x_2304_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_fst_2267_, v_fvarId_2301_, v___x_2303_);
                            if v_isShared_2270_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                                crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2304_);
                                v___x_2306_ = v___x_2269_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_2310_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2304_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2292_);
                                v___x_2306_ = v_reuseFailAlloc_2310_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_2301_);
                            crate::leanh::lean_dec_ref(v_val_2249_);
                            v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0;
                            if v_isShared_2270_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                                v___x_2313_ = v___x_2269_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2320_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_fst_2267_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2292_);
                                v___x_2313_ = v_reuseFailAlloc_2320_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2287_);
                        crate::leanh::lean_dec_ref(v_val_2249_);
                        v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0;
                        if v_isShared_2270_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                            v___x_2323_ = v___x_2269_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2330_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2267_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2292_);
                            v___x_2323_ = v_reuseFailAlloc_2330_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2297_);
                    crate::leanh::lean_dec(v___x_2287_);
                    if v_isShared_2270_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                        v___x_2332_ = v___x_2269_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_fst_2267_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___x_2292_);
                        v___x_2332_ = v_reuseFailAlloc_2336_;
                        state = 17;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2306_);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2274_);
                    v___x_2308_ = v___x_2264_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___x_2306_);
                    v___x_2308_ = v_reuseFailAlloc_2309_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_2256_ = v___x_2308_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2313_);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2311_);
                    v___x_2315_ = v___x_2264_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2313_);
                    v___x_2315_ = v_reuseFailAlloc_2319_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2298_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2297_, 0);
                    crate::leanh::lean_ctor_set(v___x_2297_, 0, v___x_2315_);
                    v___x_2317_ = v___x_2297_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
                    v___x_2317_ = v_reuseFailAlloc_2318_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2317_;
            }
            14 => {
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2323_);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2321_);
                    v___x_2325_ = v___x_2264_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2323_);
                    v___x_2325_ = v_reuseFailAlloc_2329_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2298_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2297_, 0);
                    crate::leanh::lean_ctor_set(v___x_2297_, 0, v___x_2325_);
                    v___x_2327_ = v___x_2297_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
                    v___x_2327_ = v_reuseFailAlloc_2328_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2327_;
            }
            17 => {
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2332_);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2274_);
                    v___x_2334_ = v___x_2264_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2335_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2332_);
                    v___x_2334_ = v_reuseFailAlloc_2335_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_a_2256_ = v___x_2334_;
                state = 1;
                continue;
            }
            19 => {
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2340_);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2338_);
                    v___x_2342_ = v___x_2264_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2340_);
                    v___x_2342_ = v_reuseFailAlloc_2344_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2343_, 0, v___x_2342_);
                return v___x_2343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___boxed(
    mut v_val_2354_: *mut crate::leanh::LeanObject,
    mut v_as_2355_: *mut crate::leanh::LeanObject,
    mut v_sz_2356_: *mut crate::leanh::LeanObject,
    mut v_i_2357_: *mut crate::leanh::LeanObject,
    mut v_b_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2360_: usize = 0;
    let mut v_i_boxed_2361_: usize = 0;
    let mut v_res_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2360_ = crate::leanh::lean_unbox_usize(v_sz_2356_);
    crate::leanh::lean_dec(v_sz_2356_);
    v_i_boxed_2361_ = crate::leanh::lean_unbox_usize(v_i_2357_);
    crate::leanh::lean_dec(v_i_2357_);
    v_res_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_2354_, v_as_2355_, v_sz_boxed_2360_, v_i_boxed_2361_, v_b_2358_);
    crate::leanh::lean_dec_ref(v_as_2355_);
    return v_res_2362_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ = crate::leanh::lean_box(0);
    v_dummy_2364_ = l_Lean_Expr_sort___override(v___x_2363_);
    return v_dummy_2364_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(
    mut v_e_2365_: *mut crate::leanh::LeanObject,
    mut v_decl_2366_: *mut crate::leanh::LeanObject,
    mut v_a_2367_: *mut crate::leanh::LeanObject,
    mut v_a_2368_: *mut crate::leanh::LeanObject,
    mut v_a_2369_: *mut crate::leanh::LeanObject,
    mut v_a_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvars_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v_val_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2401_: usize = 0;
    let mut v___x_2402_: usize = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v_fst_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut v_a_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut v_a_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvars_2372_ = crate::leanh::lean_ctor_get(v_decl_2366_, 0);
                v_mvarIdPending_2373_ = crate::leanh::lean_ctor_get(v_decl_2366_, 1);
                v_isSharedCheck_2441_ = (!crate::leanh::lean_is_exclusive(v_decl_2366_)) as u8;
                if v_isSharedCheck_2441_ == 0 {
                    v___x_2375_ = v_decl_2366_;
                    v_isShared_2376_ = v_isSharedCheck_2441_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarIdPending_2373_);
                    crate::leanh::lean_inc(v_fvars_2372_);
                    crate::leanh::lean_dec(v_decl_2366_);
                    v___x_2375_ = crate::leanh::lean_box(0);
                    v_isShared_2376_ = v_isSharedCheck_2441_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2377_ = l_Lean_Expr_getAppNumArgs(v_e_2365_);
                v___x_2378_ = lean_array_get_size(v_fvars_2372_);
                v___x_2379_ = lean_nat_dec_eq(v___x_2377_, v___x_2378_);
                if v___x_2379_ == 0 {
                    crate::leanh::lean_dec(v___x_2377_);
                    crate::leanh::lean_del_object(v___x_2375_);
                    crate::leanh::lean_dec(v_mvarIdPending_2373_);
                    crate::leanh::lean_dec_ref(v_fvars_2372_);
                    crate::leanh::lean_dec_ref(v_e_2365_);
                    v___x_2380_ = crate::leanh::lean_box((v___x_2379_) as usize);
                    v___x_2381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2381_, 0, v___x_2380_);
                    return v___x_2381_;
                } else {
                    v___x_2382_ =
                        l_Lean_MVarId_findDecl_x3f___redArg(v_mvarIdPending_2373_, v_a_2368_);
                    crate::leanh::lean_dec(v_mvarIdPending_2373_);
                    if crate::leanh::lean_obj_tag(v___x_2382_) == 0 {
                        v_a_2383_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2432_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2432_ == 0 {
                            v___x_2385_ = v___x_2382_;
                            v_isShared_2386_ = v_isSharedCheck_2432_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2383_);
                            crate::leanh::lean_dec(v___x_2382_);
                            v___x_2385_ = crate::leanh::lean_box(0);
                            v_isShared_2386_ = v_isSharedCheck_2432_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2377_);
                        crate::leanh::lean_del_object(v___x_2375_);
                        crate::leanh::lean_dec_ref(v_fvars_2372_);
                        crate::leanh::lean_dec_ref(v_e_2365_);
                        v_a_2433_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2440_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2440_ == 0 {
                            v___x_2435_ = v___x_2382_;
                            v_isShared_2436_ = v_isSharedCheck_2440_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2433_);
                            crate::leanh::lean_dec(v___x_2382_);
                            v___x_2435_ = crate::leanh::lean_box(0);
                            v_isShared_2436_ = v_isSharedCheck_2440_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2383_) == 1 {
                    crate::leanh::lean_del_object(v___x_2385_);
                    v_val_2387_ = crate::leanh::lean_ctor_get(v_a_2383_, 0);
                    crate::leanh::lean_inc(v_val_2387_);
                    crate::leanh::lean_dec_ref_known(v_a_2383_, 1);
                    v___x_2388_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                    v_dummy_2389_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once), _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0);
                    crate::leanh::lean_inc(v___x_2377_);
                    v___x_2390_ = lean_mk_array(v___x_2377_, v_dummy_2389_);
                    v___x_2391_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2392_ = lean_nat_sub(v___x_2377_, v___x_2391_);
                    crate::leanh::lean_dec(v___x_2377_);
                    v___x_2393_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_2365_,
                        v___x_2390_,
                        v___x_2392_,
                    );
                    v___x_2394_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2395_ = lean_array_get_size(v___x_2393_);
                    v___x_2396_ =
                        l_Array_toSubarray___redArg(v___x_2393_, v___x_2394_, v___x_2395_);
                    v___x_2397_ = crate::leanh::lean_box(0);
                    if v_isShared_2376_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2375_, 1, v___x_2396_);
                        crate::leanh::lean_ctor_set(v___x_2375_, 0, v___x_2388_);
                        v___x_2399_ = v___x_2375_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2388_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2396_);
                        v___x_2399_ = v_reuseFailAlloc_2426_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2383_);
                    crate::leanh::lean_dec(v___x_2377_);
                    crate::leanh::lean_del_object(v___x_2375_);
                    crate::leanh::lean_dec_ref(v_fvars_2372_);
                    crate::leanh::lean_dec_ref(v_e_2365_);
                    v___x_2427_ = 0;
                    v___x_2428_ = crate::leanh::lean_box((v___x_2427_) as usize);
                    if v_isShared_2386_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2385_, 0, v___x_2428_);
                        v___x_2430_ = v___x_2385_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
                        v___x_2430_ = v_reuseFailAlloc_2431_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2400_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2400_, 0, v___x_2397_);
                crate::leanh::lean_ctor_set(v___x_2400_, 1, v___x_2399_);
                v_sz_2401_ = lean_array_size(v_fvars_2372_);
                v___x_2402_ = 0usize;
                v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_2387_, v_fvars_2372_, v_sz_2401_, v___x_2402_, v___x_2400_);
                crate::leanh::lean_dec_ref(v_fvars_2372_);
                if crate::leanh::lean_obj_tag(v___x_2403_) == 0 {
                    v_a_2404_ = crate::leanh::lean_ctor_get(v___x_2403_, 0);
                    v_isSharedCheck_2417_ = (!crate::leanh::lean_is_exclusive(v___x_2403_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2406_ = v___x_2403_;
                        v_isShared_2407_ = v_isSharedCheck_2417_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2404_);
                        crate::leanh::lean_dec(v___x_2403_);
                        v___x_2406_ = crate::leanh::lean_box(0);
                        v_isShared_2407_ = v_isSharedCheck_2417_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2418_ = crate::leanh::lean_ctor_get(v___x_2403_, 0);
                    v_isSharedCheck_2425_ = (!crate::leanh::lean_is_exclusive(v___x_2403_)) as u8;
                    if v_isSharedCheck_2425_ == 0 {
                        v___x_2420_ = v___x_2403_;
                        v_isShared_2421_ = v_isSharedCheck_2425_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2418_);
                        crate::leanh::lean_dec(v___x_2403_);
                        v___x_2420_ = crate::leanh::lean_box(0);
                        v_isShared_2421_ = v_isSharedCheck_2425_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2408_ = crate::leanh::lean_ctor_get(v_a_2404_, 0);
                crate::leanh::lean_inc(v_fst_2408_);
                crate::leanh::lean_dec(v_a_2404_);
                if crate::leanh::lean_obj_tag(v_fst_2408_) == 0 {
                    v___x_2409_ = crate::leanh::lean_box((v___x_2379_) as usize);
                    if v_isShared_2407_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2406_, 0, v___x_2409_);
                        v___x_2411_ = v___x_2406_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
                        v___x_2411_ = v_reuseFailAlloc_2412_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_2413_ = crate::leanh::lean_ctor_get(v_fst_2408_, 0);
                    crate::leanh::lean_inc(v_val_2413_);
                    crate::leanh::lean_dec_ref_known(v_fst_2408_, 1);
                    if v_isShared_2407_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2406_, 0, v_val_2413_);
                        v___x_2415_ = v___x_2406_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_val_2413_);
                        v___x_2415_ = v_reuseFailAlloc_2416_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2411_;
            }
            6 => {
                return v___x_2415_;
            }
            7 => {
                if v_isShared_2421_ == 0 {
                    v___x_2423_ = v___x_2420_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
                    v___x_2423_ = v_reuseFailAlloc_2424_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2423_;
            }
            9 => {
                return v___x_2430_;
            }
            10 => {
                if v_isShared_2436_ == 0 {
                    v___x_2438_ = v___x_2435_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
                    v___x_2438_ = v_reuseFailAlloc_2439_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___boxed(
    mut v_e_2442_: *mut crate::leanh::LeanObject,
    mut v_decl_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
    mut v_a_2446_: *mut crate::leanh::LeanObject,
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(
        v_e_2442_,
        v_decl_2443_,
        v_a_2444_,
        v_a_2445_,
        v_a_2446_,
        v_a_2447_,
    );
    crate::leanh::lean_dec(v_a_2447_);
    crate::leanh::lean_dec_ref(v_a_2446_);
    crate::leanh::lean_dec(v_a_2445_);
    crate::leanh::lean_dec_ref(v_a_2444_);
    return v_res_2449_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(
    mut v_00_u03b2_2450_: *mut crate::leanh::LeanObject,
    mut v_m_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2453_: u8 = 0;
    v___x_2453_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_2451_, v_a_2452_);
    return v___x_2453_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___boxed(
    mut v_00_u03b2_2454_: *mut crate::leanh::LeanObject,
    mut v_m_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2457_: u8 = 0;
    let mut v_r_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2457_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(v_00_u03b2_2454_, v_m_2455_, v_a_2456_);
    crate::leanh::lean_dec(v_a_2456_);
    crate::leanh::lean_dec_ref(v_m_2455_);
    v_r_2458_ = crate::leanh::lean_box((v_res_2457_) as usize);
    return v_r_2458_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(
    mut v_00_u03b2_2459_: *mut crate::leanh::LeanObject,
    mut v_m_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_b_2462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_m_2460_, v_a_2461_, v_b_2462_);
    return v___x_2463_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(
    mut v_val_2464_: *mut crate::leanh::LeanObject,
    mut v_as_2465_: *mut crate::leanh::LeanObject,
    mut v_sz_2466_: usize,
    mut v_i_2467_: usize,
    mut v_b_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
    mut v___y_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_2464_, v_as_2465_, v_sz_2466_, v_i_2467_, v_b_2468_);
    return v___x_2474_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___boxed(
    mut v_val_2475_: *mut crate::leanh::LeanObject,
    mut v_as_2476_: *mut crate::leanh::LeanObject,
    mut v_sz_2477_: *mut crate::leanh::LeanObject,
    mut v_i_2478_: *mut crate::leanh::LeanObject,
    mut v_b_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
    mut v___y_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2485_: usize = 0;
    let mut v_i_boxed_2486_: usize = 0;
    let mut v_res_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2485_ = crate::leanh::lean_unbox_usize(v_sz_2477_);
    crate::leanh::lean_dec(v_sz_2477_);
    v_i_boxed_2486_ = crate::leanh::lean_unbox_usize(v_i_2478_);
    crate::leanh::lean_dec(v_i_2478_);
    v_res_2487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(v_val_2475_, v_as_2476_, v_sz_boxed_2485_, v_i_boxed_2486_, v_b_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
    crate::leanh::lean_dec(v___y_2483_);
    crate::leanh::lean_dec_ref(v___y_2482_);
    crate::leanh::lean_dec(v___y_2481_);
    crate::leanh::lean_dec_ref(v___y_2480_);
    crate::leanh::lean_dec_ref(v_as_2476_);
    return v_res_2487_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(
    mut v_00_u03b2_2488_: *mut crate::leanh::LeanObject,
    mut v_a_2489_: *mut crate::leanh::LeanObject,
    mut v_x_2490_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2491_: u8 = 0;
    v___x_2491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_2489_, v_x_2490_);
    return v___x_2491_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___boxed(
    mut v_00_u03b2_2492_: *mut crate::leanh::LeanObject,
    mut v_a_2493_: *mut crate::leanh::LeanObject,
    mut v_x_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2495_: u8 = 0;
    let mut v_r_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(v_00_u03b2_2492_, v_a_2493_, v_x_2494_);
    crate::leanh::lean_dec(v_x_2494_);
    crate::leanh::lean_dec(v_a_2493_);
    v_r_2496_ = crate::leanh::lean_box((v_res_2495_) as usize);
    return v_r_2496_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(
    mut v_00_u03b2_2497_: *mut crate::leanh::LeanObject,
    mut v_data_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_data_2498_);
    return v___x_2499_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2500_: *mut crate::leanh::LeanObject,
    mut v_i_2501_: *mut crate::leanh::LeanObject,
    mut v_source_2502_: *mut crate::leanh::LeanObject,
    mut v_target_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2504_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v_i_2501_, v_source_2502_, v_target_2503_);
    return v___x_2504_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_2505_: *mut crate::leanh::LeanObject,
    mut v_x_2506_: *mut crate::leanh::LeanObject,
    mut v_x_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_x_2506_, v_x_2507_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(
    mut v_mvarId_2509_: *mut crate::leanh::LeanObject,
    mut v___y_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2512_ = lean_st_ref_get(v___y_2510_);
    v_mctx_2513_ = crate::leanh::lean_ctor_get(v___x_2512_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2513_);
    crate::leanh::lean_dec(v___x_2512_);
    v___x_2514_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_2513_, v_mvarId_2509_);
    crate::leanh::lean_dec_ref(v_mctx_2513_);
    v___x_2515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2514_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg___boxed(
    mut v_mvarId_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2519_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_2516_, v___y_2517_);
    crate::leanh::lean_dec(v___y_2517_);
    crate::leanh::lean_dec(v_mvarId_2516_);
    return v_res_2519_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(
    mut v_mvarId_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2526_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_2520_, v___y_2522_);
    return v___x_2526_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___boxed(
    mut v_mvarId_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
    mut v___y_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(v_mvarId_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
    crate::leanh::lean_dec(v___y_2531_);
    crate::leanh::lean_dec_ref(v___y_2530_);
    crate::leanh::lean_dec(v___y_2529_);
    crate::leanh::lean_dec_ref(v___y_2528_);
    crate::leanh::lean_dec(v_mvarId_2527_);
    return v_res_2533_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(
    mut v_e_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut v_unused_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2537_ = l_Lean_Expr_hasMVar(v_e_2534_);
                if v___x_2537_ == 0 {
                    v___x_2538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2538_, 0, v_e_2534_);
                    return v___x_2538_;
                } else {
                    v___x_2539_ = lean_st_ref_get(v___y_2535_);
                    v_mctx_2540_ = crate::leanh::lean_ctor_get(v___x_2539_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2540_);
                    crate::leanh::lean_dec(v___x_2539_);
                    v___x_2541_ = l_Lean_instantiateMVarsCore(v_mctx_2540_, v_e_2534_);
                    v_fst_2542_ = crate::leanh::lean_ctor_get(v___x_2541_, 0);
                    crate::leanh::lean_inc(v_fst_2542_);
                    v_snd_2543_ = crate::leanh::lean_ctor_get(v___x_2541_, 1);
                    crate::leanh::lean_inc(v_snd_2543_);
                    crate::leanh::lean_dec_ref(v___x_2541_);
                    v___x_2544_ = lean_st_ref_take(v___y_2535_);
                    v_cache_2545_ = crate::leanh::lean_ctor_get(v___x_2544_, 1);
                    v_zetaDeltaFVarIds_2546_ = crate::leanh::lean_ctor_get(v___x_2544_, 2);
                    v_postponed_2547_ = crate::leanh::lean_ctor_get(v___x_2544_, 3);
                    v_diag_2548_ = crate::leanh::lean_ctor_get(v___x_2544_, 4);
                    v_isSharedCheck_2557_ = (!crate::leanh::lean_is_exclusive(v___x_2544_)) as u8;
                    if v_isSharedCheck_2557_ == 0 {
                        v_unused_2558_ = crate::leanh::lean_ctor_get(v___x_2544_, 0);
                        crate::leanh::lean_dec(v_unused_2558_);
                        v___x_2550_ = v___x_2544_;
                        v_isShared_2551_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2548_);
                        crate::leanh::lean_inc(v_postponed_2547_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2546_);
                        crate::leanh::lean_inc(v_cache_2545_);
                        crate::leanh::lean_dec(v___x_2544_);
                        v___x_2550_ = crate::leanh::lean_box(0);
                        v_isShared_2551_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2550_, 0, v_snd_2543_);
                    v___x_2553_ = v___x_2550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_snd_2543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_cache_2545_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2556_,
                        2,
                        v_zetaDeltaFVarIds_2546_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_postponed_2547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 4, v_diag_2548_);
                    v___x_2553_ = v_reuseFailAlloc_2556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2554_ = lean_st_ref_set(v___y_2535_, v___x_2553_);
                v___x_2555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2555_, 0, v_fst_2542_);
                return v___x_2555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg___boxed(
    mut v_e_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_2559_, v___y_2560_);
    crate::leanh::lean_dec(v___y_2560_);
    return v_res_2562_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(
    mut v_e_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2569_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_2563_, v___y_2565_);
    return v___x_2569_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___boxed(
    mut v_e_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(v_e_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
    crate::leanh::lean_dec(v___y_2574_);
    crate::leanh::lean_dec_ref(v___y_2573_);
    crate::leanh::lean_dec(v___y_2572_);
    crate::leanh::lean_dec_ref(v___y_2571_);
    return v_res_2576_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(
    mut v_mvarId_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2580_ = lean_st_ref_get(v___y_2578_);
    v_mctx_2581_ = crate::leanh::lean_ctor_get(v___x_2580_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2581_);
    crate::leanh::lean_dec(v___x_2580_);
    v___x_2582_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_2581_, v_mvarId_2577_);
    crate::leanh::lean_dec_ref(v_mctx_2581_);
    v___x_2583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2583_, 0, v___x_2582_);
    return v___x_2583_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg___boxed(
    mut v_mvarId_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_2584_, v___y_2585_);
    crate::leanh::lean_dec(v___y_2585_);
    crate::leanh::lean_dec(v_mvarId_2584_);
    return v_res_2587_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(
    mut v_mvarId_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_2588_, v___y_2590_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___boxed(
    mut v_mvarId_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2601_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(v_mvarId_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
    crate::leanh::lean_dec(v___y_2599_);
    crate::leanh::lean_dec_ref(v___y_2598_);
    crate::leanh::lean_dec(v___y_2597_);
    crate::leanh::lean_dec_ref(v___y_2596_);
    crate::leanh::lean_dec(v_mvarId_2595_);
    return v_res_2601_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(
    mut v_mvarIdPending_2602_: *mut crate::leanh::LeanObject,
    mut v_a_2603_: *mut crate::leanh::LeanObject,
    mut v_a_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v_val_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v_val_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_a_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v_a_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2668_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_a_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_a_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2608_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarIdPending_2602_, v_a_2604_);
                if crate::leanh::lean_obj_tag(v___x_2608_) == 0 {
                    v_a_2609_ = crate::leanh::lean_ctor_get(v___x_2608_, 0);
                    v_isSharedCheck_2684_ = (!crate::leanh::lean_is_exclusive(v___x_2608_)) as u8;
                    if v_isSharedCheck_2684_ == 0 {
                        v___x_2611_ = v___x_2608_;
                        v_isShared_2612_ = v_isSharedCheck_2684_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2609_);
                        crate::leanh::lean_dec(v___x_2608_);
                        v___x_2611_ = crate::leanh::lean_box(0);
                        v_isShared_2612_ = v_isSharedCheck_2684_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarIdPending_2602_);
                    v_a_2685_ = crate::leanh::lean_ctor_get(v___x_2608_, 0);
                    v_isSharedCheck_2692_ = (!crate::leanh::lean_is_exclusive(v___x_2608_)) as u8;
                    if v_isSharedCheck_2692_ == 0 {
                        v___x_2687_ = v___x_2608_;
                        v_isShared_2688_ = v_isSharedCheck_2692_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2685_);
                        crate::leanh::lean_dec(v___x_2608_);
                        v___x_2687_ = crate::leanh::lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2692_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2609_) == 1 {
                    v_val_2613_ = crate::leanh::lean_ctor_get(v_a_2609_, 0);
                    crate::leanh::lean_inc(v_val_2613_);
                    crate::leanh::lean_dec_ref_known(v_a_2609_, 1);
                    v___x_2614_ = l_Lean_Expr_getAppFn_x27(v_val_2613_);
                    v___x_2615_ = l_Lean_Expr_isMVar(v___x_2614_);
                    crate::leanh::lean_dec_ref(v___x_2614_);
                    if v___x_2615_ == 0 {
                        crate::leanh::lean_dec(v_val_2613_);
                        if v_isShared_2612_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2611_, 0, v_mvarIdPending_2602_);
                            v___x_2617_ = v___x_2611_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2618_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2618_,
                                0,
                                v_mvarIdPending_2602_,
                            );
                            v___x_2617_ = v_reuseFailAlloc_2618_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2611_);
                        v___x_2619_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_val_2613_, v_a_2604_);
                        if crate::leanh::lean_obj_tag(v___x_2619_) == 0 {
                            v_a_2620_ = crate::leanh::lean_ctor_get(v___x_2619_, 0);
                            v_isSharedCheck_2672_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2619_)) as u8;
                            if v_isSharedCheck_2672_ == 0 {
                                v___x_2622_ = v___x_2619_;
                                v_isShared_2623_ = v_isSharedCheck_2672_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2620_);
                                crate::leanh::lean_dec(v___x_2619_);
                                v___x_2622_ = crate::leanh::lean_box(0);
                                v_isShared_2623_ = v_isSharedCheck_2672_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarIdPending_2602_);
                            v_a_2673_ = crate::leanh::lean_ctor_get(v___x_2619_, 0);
                            v_isSharedCheck_2680_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2619_)) as u8;
                            if v_isSharedCheck_2680_ == 0 {
                                v___x_2675_ = v___x_2619_;
                                v_isShared_2676_ = v_isSharedCheck_2680_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2673_);
                                crate::leanh::lean_dec(v___x_2619_);
                                v___x_2675_ = crate::leanh::lean_box(0);
                                v_isShared_2676_ = v_isSharedCheck_2680_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2609_);
                    if v_isShared_2612_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2611_, 0, v_mvarIdPending_2602_);
                        v___x_2682_ = v___x_2611_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2683_,
                            0,
                            v_mvarIdPending_2602_,
                        );
                        v___x_2682_ = v_reuseFailAlloc_2683_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2617_;
            }
            3 => {
                v___x_2624_ = l_Lean_Expr_consumeMData(v_a_2620_);
                crate::leanh::lean_dec(v_a_2620_);
                if crate::leanh::lean_obj_tag(v___x_2624_) == 2 {
                    crate::leanh::lean_dec(v_mvarIdPending_2602_);
                    v_mvarId_2625_ = crate::leanh::lean_ctor_get(v___x_2624_, 0);
                    crate::leanh::lean_inc(v_mvarId_2625_);
                    crate::leanh::lean_dec_ref_known(v___x_2624_, 1);
                    if v_isShared_2623_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2622_, 0, v_mvarId_2625_);
                        v___x_2627_ = v___x_2622_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2628_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_mvarId_2625_);
                        v___x_2627_ = v_reuseFailAlloc_2628_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2629_ = l_Lean_Expr_getAppFn_x27(v___x_2624_);
                    if crate::leanh::lean_obj_tag(v___x_2629_) == 2 {
                        crate::leanh::lean_del_object(v___x_2622_);
                        v_mvarId_2630_ = crate::leanh::lean_ctor_get(v___x_2629_, 0);
                        crate::leanh::lean_inc(v_mvarId_2630_);
                        crate::leanh::lean_dec_ref_known(v___x_2629_, 1);
                        v___x_2631_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_2630_, v_a_2604_);
                        crate::leanh::lean_dec(v_mvarId_2630_);
                        if crate::leanh::lean_obj_tag(v___x_2631_) == 0 {
                            v_a_2632_ = crate::leanh::lean_ctor_get(v___x_2631_, 0);
                            v_isSharedCheck_2660_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2631_)) as u8;
                            if v_isSharedCheck_2660_ == 0 {
                                v___x_2634_ = v___x_2631_;
                                v_isShared_2635_ = v_isSharedCheck_2660_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2632_);
                                crate::leanh::lean_dec(v___x_2631_);
                                v___x_2634_ = crate::leanh::lean_box(0);
                                v_isShared_2635_ = v_isSharedCheck_2660_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2624_);
                            crate::leanh::lean_dec(v_mvarIdPending_2602_);
                            v_a_2661_ = crate::leanh::lean_ctor_get(v___x_2631_, 0);
                            v_isSharedCheck_2668_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2631_)) as u8;
                            if v_isSharedCheck_2668_ == 0 {
                                v___x_2663_ = v___x_2631_;
                                v_isShared_2664_ = v_isSharedCheck_2668_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2661_);
                                crate::leanh::lean_dec(v___x_2631_);
                                v___x_2663_ = crate::leanh::lean_box(0);
                                v_isShared_2664_ = v_isSharedCheck_2668_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2629_);
                        crate::leanh::lean_dec_ref(v___x_2624_);
                        if v_isShared_2623_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2622_, 0, v_mvarIdPending_2602_);
                            v___x_2670_ = v___x_2622_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_2671_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2671_,
                                0,
                                v_mvarIdPending_2602_,
                            );
                            v___x_2670_ = v_reuseFailAlloc_2671_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_2627_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_2632_) == 1 {
                    crate::leanh::lean_del_object(v___x_2634_);
                    v_val_2636_ = crate::leanh::lean_ctor_get(v_a_2632_, 0);
                    crate::leanh::lean_inc_n(v_val_2636_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_2632_, 1);
                    v___x_2637_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(
                        v___x_2624_,
                        v_val_2636_,
                        v_a_2603_,
                        v_a_2604_,
                        v_a_2605_,
                        v_a_2606_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2637_) == 0 {
                        v_a_2638_ = crate::leanh::lean_ctor_get(v___x_2637_, 0);
                        v_isSharedCheck_2648_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2637_)) as u8;
                        if v_isSharedCheck_2648_ == 0 {
                            v___x_2640_ = v___x_2637_;
                            v_isShared_2641_ = v_isSharedCheck_2648_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2638_);
                            crate::leanh::lean_dec(v___x_2637_);
                            v___x_2640_ = crate::leanh::lean_box(0);
                            v_isShared_2641_ = v_isSharedCheck_2648_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2636_);
                        crate::leanh::lean_dec(v_mvarIdPending_2602_);
                        v_a_2649_ = crate::leanh::lean_ctor_get(v___x_2637_, 0);
                        v_isSharedCheck_2656_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2637_)) as u8;
                        if v_isSharedCheck_2656_ == 0 {
                            v___x_2651_ = v___x_2637_;
                            v_isShared_2652_ = v_isSharedCheck_2656_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2649_);
                            crate::leanh::lean_dec(v___x_2637_);
                            v___x_2651_ = crate::leanh::lean_box(0);
                            v_isShared_2652_ = v_isSharedCheck_2656_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2632_);
                    crate::leanh::lean_dec_ref(v___x_2624_);
                    if v_isShared_2635_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2634_, 0, v_mvarIdPending_2602_);
                        v___x_2658_ = v___x_2634_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2659_,
                            0,
                            v_mvarIdPending_2602_,
                        );
                        v___x_2658_ = v_reuseFailAlloc_2659_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2642_ = (crate::leanh::lean_unbox(v_a_2638_) as u8);
                crate::leanh::lean_dec(v_a_2638_);
                if v___x_2642_ == 0 {
                    crate::leanh::lean_dec(v_val_2636_);
                    if v_isShared_2641_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2640_, 0, v_mvarIdPending_2602_);
                        v___x_2644_ = v___x_2640_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2645_,
                            0,
                            v_mvarIdPending_2602_,
                        );
                        v___x_2644_ = v_reuseFailAlloc_2645_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2640_);
                    crate::leanh::lean_dec(v_mvarIdPending_2602_);
                    v_mvarIdPending_2646_ = crate::leanh::lean_ctor_get(v_val_2636_, 1);
                    crate::leanh::lean_inc(v_mvarIdPending_2646_);
                    crate::leanh::lean_dec(v_val_2636_);
                    v_mvarIdPending_2602_ = v_mvarIdPending_2646_;
                    state = 0;
                    continue;
                }
            }
            7 => {
                return v___x_2644_;
            }
            8 => {
                if v_isShared_2652_ == 0 {
                    v___x_2654_ = v___x_2651_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
                    v___x_2654_ = v_reuseFailAlloc_2655_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2654_;
            }
            10 => {
                return v___x_2658_;
            }
            11 => {
                if v_isShared_2664_ == 0 {
                    v___x_2666_ = v___x_2663_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
                    v___x_2666_ = v_reuseFailAlloc_2667_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2666_;
            }
            13 => {
                return v___x_2670_;
            }
            14 => {
                if v_isShared_2676_ == 0 {
                    v___x_2678_ = v___x_2675_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
                    v___x_2678_ = v_reuseFailAlloc_2679_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2678_;
            }
            16 => {
                return v___x_2682_;
            }
            17 => {
                if v_isShared_2688_ == 0 {
                    v___x_2690_ = v___x_2687_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending___boxed(
    mut v_mvarIdPending_2693_: *mut crate::leanh::LeanObject,
    mut v_a_2694_: *mut crate::leanh::LeanObject,
    mut v_a_2695_: *mut crate::leanh::LeanObject,
    mut v_a_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(
        v_mvarIdPending_2693_,
        v_a_2694_,
        v_a_2695_,
        v_a_2696_,
        v_a_2697_,
    );
    crate::leanh::lean_dec(v_a_2697_);
    crate::leanh::lean_dec_ref(v_a_2696_);
    crate::leanh::lean_dec(v_a_2695_);
    crate::leanh::lean_dec_ref(v_a_2694_);
    return v_res_2699_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(
    mut v_n_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0;
    v___x_2703_ = lean_string_append(v___x_2702_, v_n_2701_);
    v___x_2704_ = lean_string_append(v___x_2703_, v___x_2702_);
    return v___x_2704_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___boxed(
    mut v_n_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2706_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_n_2705_);
    crate::leanh::lean_dec_ref(v_n_2705_);
    return v_res_2706_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(
    mut v_a_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___y_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: u8 = 0;
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2707_) == 0 {
                    v___x_2709_ = l_List_reverse___redArg(v_a_2708_);
                    return v___x_2709_;
                } else {
                    v_head_2710_ = crate::leanh::lean_ctor_get(v_a_2707_, 0);
                    v_tail_2711_ = crate::leanh::lean_ctor_get(v_a_2707_, 1);
                    v_isSharedCheck_2730_ = (!crate::leanh::lean_is_exclusive(v_a_2707_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v___x_2713_ = v_a_2707_;
                        v_isShared_2714_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2711_);
                        crate::leanh::lean_inc(v_head_2710_);
                        crate::leanh::lean_dec(v_a_2707_);
                        v___x_2713_ = crate::leanh::lean_box(0);
                        v_isShared_2714_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2721_ = l_Lean_Name_hasMacroScopes(v_head_2710_);
                v___x_2722_ = 1;
                if v___x_2721_ == 0 {
                    v___x_2723_ = l_Lean_Name_toString(v_head_2710_, v___x_2722_);
                    v___x_2724_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_2723_);
                    crate::leanh::lean_dec_ref(v___x_2723_);
                    v___y_2716_ = v___x_2724_;
                    state = 2;
                    continue;
                } else {
                    v___x_2725_ = lean_erase_macro_scopes(v_head_2710_);
                    v___x_2726_ = l_Lean_Name_toString(v___x_2725_, v___x_2722_);
                    v___x_2727_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0;
                    v___x_2728_ = lean_string_append(v___x_2726_, v___x_2727_);
                    v___x_2729_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_2728_);
                    crate::leanh::lean_dec_ref(v___x_2728_);
                    v___y_2716_ = v___x_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2714_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2713_, 1, v_a_2708_);
                    crate::leanh::lean_ctor_set(v___x_2713_, 0, v___y_2716_);
                    v___x_2718_ = v___x_2713_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___y_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_a_2708_);
                    v___x_2718_ = v_reuseFailAlloc_2720_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_2707_ = v_tail_2711_;
                v_a_2708_ = v___x_2718_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(
    mut v_ns_2732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0;
    v___x_2734_ = crate::leanh::lean_box(0);
    v___x_2735_ = l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(v_ns_2732_, v___x_2734_);
    v___x_2736_ = l_String_intercalate(v___x_2733_, v___x_2735_);
    return v___x_2736_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(
    mut v_count_2737_: *mut crate::leanh::LeanObject,
    mut v_singular_2738_: *mut crate::leanh::LeanObject,
    mut v_plural_2739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    v___x_2740_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2741_ = lean_nat_dec_eq(v_count_2737_, v___x_2740_);
    if v___x_2741_ == 0 {
        crate::leanh::lean_inc_ref(v_plural_2739_);
        return v_plural_2739_;
    } else {
        crate::leanh::lean_inc_ref(v_singular_2738_);
        return v_singular_2738_;
    }
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1___boxed(
    mut v_count_2742_: *mut crate::leanh::LeanObject,
    mut v_singular_2743_: *mut crate::leanh::LeanObject,
    mut v_plural_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v_count_2742_, v_singular_2743_, v_plural_2744_);
    crate::leanh::lean_dec_ref(v_plural_2744_);
    crate::leanh::lean_dec_ref(v_singular_2743_);
    crate::leanh::lean_dec(v_count_2742_);
    return v_res_2745_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(
    mut v___x_2746_: *mut crate::leanh::LeanObject,
    mut v_as_2747_: *mut crate::leanh::LeanObject,
    mut v_i_2748_: usize,
    mut v_stop_2749_: usize,
    mut v_b_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_2753_: usize = 0;
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: u8 = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2751_ = lean_usize_dec_eq(v_i_2748_, v_stop_2749_);
                if v___x_2751_ == 0 {
                    v___x_2752_ = 1usize;
                    v___x_2753_ = lean_usize_sub(v_i_2748_, v___x_2752_);
                    v___x_2754_ = lean_array_uget_borrowed(v_as_2747_, v___x_2753_);
                    if crate::leanh::lean_obj_tag(v___x_2754_) == 0 {
                        v_i_2748_ = v___x_2753_;
                        state = 0;
                        continue;
                    } else {
                        v_val_2756_ = crate::leanh::lean_ctor_get(v___x_2754_, 0);
                        v___x_2757_ = l_Lean_LocalDecl_fvarId(v_val_2756_);
                        v___x_2758_ = l_Lean_LocalContext_contains(v___x_2746_, v___x_2757_);
                        crate::leanh::lean_dec(v___x_2757_);
                        if v___x_2758_ == 0 {
                            v___x_2759_ = l_Lean_LocalDecl_userName(v_val_2756_);
                            v___x_2760_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2760_, 0, v___x_2759_);
                            crate::leanh::lean_ctor_set(v___x_2760_, 1, v_b_2750_);
                            v_i_2748_ = v___x_2753_;
                            v_b_2750_ = v___x_2760_;
                            state = 0;
                            continue;
                        } else {
                            v_i_2748_ = v___x_2753_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    return v_b_2750_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3___boxed(
    mut v___x_2763_: *mut crate::leanh::LeanObject,
    mut v_as_2764_: *mut crate::leanh::LeanObject,
    mut v_i_2765_: *mut crate::leanh::LeanObject,
    mut v_stop_2766_: *mut crate::leanh::LeanObject,
    mut v_b_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2768_: usize = 0;
    let mut v_stop_boxed_2769_: usize = 0;
    let mut v_res_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2768_ = crate::leanh::lean_unbox_usize(v_i_2765_);
    crate::leanh::lean_dec(v_i_2765_);
    v_stop_boxed_2769_ = crate::leanh::lean_unbox_usize(v_stop_2766_);
    crate::leanh::lean_dec(v_stop_2766_);
    v_res_2770_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_2763_, v_as_2764_, v_i_boxed_2768_, v_stop_boxed_2769_, v_b_2767_);
    crate::leanh::lean_dec_ref(v_as_2764_);
    crate::leanh::lean_dec_ref(v___x_2763_);
    return v_res_2770_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(
    mut v___x_2771_: *mut crate::leanh::LeanObject,
    mut v_x_2772_: *mut crate::leanh::LeanObject,
    mut v_x_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2772_) == 0 {
        let mut v_cs_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2777_: u8 = 0;
        v_cs_2774_ = crate::leanh::lean_ctor_get(v_x_2772_, 0);
        v___x_2775_ = lean_array_get_size(v_cs_2774_);
        v___x_2776_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2777_ = lean_nat_dec_lt(v___x_2776_, v___x_2775_);
        if v___x_2777_ == 0 {
            return v_x_2773_;
        } else {
            let mut v___x_2778_: usize = 0;
            let mut v___x_2779_: usize = 0;
            let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2778_ = lean_usize_of_nat(v___x_2775_);
            v___x_2779_ = 0usize;
            v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_2771_, v_cs_2774_, v___x_2778_, v___x_2779_, v_x_2773_);
            return v___x_2780_;
        }
    } else {
        let mut v_vs_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2784_: u8 = 0;
        v_vs_2781_ = crate::leanh::lean_ctor_get(v_x_2772_, 0);
        v___x_2782_ = lean_array_get_size(v_vs_2781_);
        v___x_2783_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2784_ = lean_nat_dec_lt(v___x_2783_, v___x_2782_);
        if v___x_2784_ == 0 {
            return v_x_2773_;
        } else {
            let mut v___x_2785_: usize = 0;
            let mut v___x_2786_: usize = 0;
            let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2785_ = lean_usize_of_nat(v___x_2782_);
            v___x_2786_ = 0usize;
            v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_2771_, v_vs_2781_, v___x_2785_, v___x_2786_, v_x_2773_);
            return v___x_2787_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(
    mut v___x_2788_: *mut crate::leanh::LeanObject,
    mut v_as_2789_: *mut crate::leanh::LeanObject,
    mut v_i_2790_: usize,
    mut v_stop_2791_: usize,
    mut v_b_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2794_: usize = 0;
    let mut v___x_2795_: usize = 0;
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2793_ = lean_usize_dec_eq(v_i_2790_, v_stop_2791_);
                if v___x_2793_ == 0 {
                    v___x_2794_ = 1usize;
                    v___x_2795_ = lean_usize_sub(v_i_2790_, v___x_2794_);
                    v___x_2796_ = lean_array_uget_borrowed(v_as_2789_, v___x_2795_);
                    v___x_2797_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_2788_, v___x_2796_, v_b_2792_);
                    v_i_2790_ = v___x_2795_;
                    v_b_2792_ = v___x_2797_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2792_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v___x_2799_: *mut crate::leanh::LeanObject,
    mut v_as_2800_: *mut crate::leanh::LeanObject,
    mut v_i_2801_: *mut crate::leanh::LeanObject,
    mut v_stop_2802_: *mut crate::leanh::LeanObject,
    mut v_b_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2804_: usize = 0;
    let mut v_stop_boxed_2805_: usize = 0;
    let mut v_res_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2804_ = crate::leanh::lean_unbox_usize(v_i_2801_);
    crate::leanh::lean_dec(v_i_2801_);
    v_stop_boxed_2805_ = crate::leanh::lean_unbox_usize(v_stop_2802_);
    crate::leanh::lean_dec(v_stop_2802_);
    v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_2799_, v_as_2800_, v_i_boxed_2804_, v_stop_boxed_2805_, v_b_2803_);
    crate::leanh::lean_dec_ref(v_as_2800_);
    crate::leanh::lean_dec_ref(v___x_2799_);
    return v_res_2806_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2___boxed(
    mut v___x_2807_: *mut crate::leanh::LeanObject,
    mut v_x_2808_: *mut crate::leanh::LeanObject,
    mut v_x_2809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_2807_, v_x_2808_, v_x_2809_);
    crate::leanh::lean_dec_ref(v_x_2808_);
    crate::leanh::lean_dec_ref(v___x_2807_);
    return v_res_2810_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(
    mut v___x_2811_: *mut crate::leanh::LeanObject,
    mut v_t_2812_: *mut crate::leanh::LeanObject,
    mut v_init_2813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    v_root_2814_ = crate::leanh::lean_ctor_get(v_t_2812_, 0);
    v_tail_2815_ = crate::leanh::lean_ctor_get(v_t_2812_, 1);
    v___x_2816_ = lean_array_get_size(v_tail_2815_);
    v___x_2817_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2818_ = lean_nat_dec_lt(v___x_2817_, v___x_2816_);
    if v___x_2818_ == 0 {
        let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2819_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_2811_, v_root_2814_, v_init_2813_);
        return v___x_2819_;
    } else {
        let mut v___x_2820_: usize = 0;
        let mut v___x_2821_: usize = 0;
        let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2820_ = lean_usize_of_nat(v___x_2816_);
        v___x_2821_ = 0usize;
        v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_2811_, v_tail_2815_, v___x_2820_, v___x_2821_, v_init_2813_);
        v___x_2823_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_2811_, v_root_2814_, v___x_2822_);
        return v___x_2823_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0___boxed(
    mut v___x_2824_: *mut crate::leanh::LeanObject,
    mut v_t_2825_: *mut crate::leanh::LeanObject,
    mut v_init_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_2824_, v_t_2825_, v_init_2826_);
    crate::leanh::lean_dec_ref(v_t_2825_);
    crate::leanh::lean_dec_ref(v___x_2824_);
    return v_res_2827_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(
    mut v___x_2828_: *mut crate::leanh::LeanObject,
    mut v_lctx_2829_: *mut crate::leanh::LeanObject,
    mut v_init_2830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_2831_ = crate::leanh::lean_ctor_get(v_lctx_2829_, 1);
    v___x_2832_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_2828_, v_decls_2831_, v_init_2830_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0___boxed(
    mut v___x_2833_: *mut crate::leanh::LeanObject,
    mut v_lctx_2834_: *mut crate::leanh::LeanObject,
    mut v_init_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v___x_2833_, v_lctx_2834_, v_init_2835_);
    crate::leanh::lean_dec_ref(v_lctx_2834_);
    crate::leanh::lean_dec_ref(v___x_2833_);
    return v_res_2836_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(
    mut v_mdecl_2842_: *mut crate::leanh::LeanObject,
    mut v_a_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    v_lctx_2845_ = crate::leanh::lean_ctor_get(v_a_2843_, 2);
    v_lctx_2846_ = crate::leanh::lean_ctor_get(v_mdecl_2842_, 1);
    v___x_2847_ = crate::leanh::lean_box(0);
    v___x_2848_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v_lctx_2845_, v_lctx_2846_, v___x_2847_);
    v___x_2849_ = l_List_isEmpty___redArg(v___x_2848_);
    if v___x_2849_ == 0 {
        let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2850_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0;
        v___x_2851_ = l_List_lengthTR___redArg(v___x_2848_);
        v___x_2852_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1;
        v___x_2853_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2;
        v___x_2854_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_2851_, v___x_2852_, v___x_2853_);
        crate::leanh::lean_dec(v___x_2851_);
        v___x_2855_ = lean_string_append(v___x_2850_, v___x_2854_);
        crate::leanh::lean_dec_ref(v___x_2854_);
        v___x_2856_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3;
        v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
        v___x_2858_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_2848_);
        v___x_2859_ = lean_string_append(v___x_2857_, v___x_2858_);
        crate::leanh::lean_dec_ref(v___x_2858_);
        v___x_2860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2860_, 0, v___x_2859_);
        return v___x_2860_;
    } else {
        let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2848_);
        v___x_2861_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4;
        v___x_2862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2862_, 0, v___x_2861_);
        return v___x_2862_;
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___boxed(
    mut v_mdecl_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2866_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_2863_, v_a_2864_);
    crate::leanh::lean_dec_ref(v_a_2864_);
    crate::leanh::lean_dec_ref(v_mdecl_2863_);
    return v_res_2866_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(
    mut v_mdecl_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_a_2869_: *mut crate::leanh::LeanObject,
    mut v_a_2870_: *mut crate::leanh::LeanObject,
    mut v_a_2871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2873_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_2867_, v_a_2868_);
    return v___x_2873_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___boxed(
    mut v_mdecl_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
    mut v_a_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: *mut crate::leanh::LeanObject,
    mut v_a_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2880_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(v_mdecl_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
    crate::leanh::lean_dec(v_a_2878_);
    crate::leanh::lean_dec_ref(v_a_2877_);
    crate::leanh::lean_dec(v_a_2876_);
    crate::leanh::lean_dec_ref(v_a_2875_);
    crate::leanh::lean_dec_ref(v_mdecl_2874_);
    return v_res_2880_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(
    mut v_lctxInitIndices_2881_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2882_: *mut crate::leanh::LeanObject,
    mut v_as_2883_: *mut crate::leanh::LeanObject,
    mut v_i_2884_: usize,
    mut v_stop_2885_: usize,
    mut v_b_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: usize = 0;
    let mut v___x_2889_: usize = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: u8 = 0;
    let mut v_lctx_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2887_ = lean_usize_dec_eq(v_i_2884_, v_stop_2885_);
                if v___x_2887_ == 0 {
                    v___x_2888_ = 1usize;
                    v___x_2889_ = lean_usize_sub(v_i_2884_, v___x_2888_);
                    v___x_2890_ = lean_array_uget_borrowed(v_as_2883_, v___x_2889_);
                    if crate::leanh::lean_obj_tag(v___x_2890_) == 0 {
                        v_i_2884_ = v___x_2889_;
                        state = 0;
                        continue;
                    } else {
                        v_val_2892_ = crate::leanh::lean_ctor_get(v___x_2890_, 0);
                        v___x_2899_ = l_Lean_LocalDecl_index(v_val_2892_);
                        v___x_2900_ = lean_nat_dec_le(v_lctxInitIndices_2881_, v___x_2899_);
                        crate::leanh::lean_dec(v___x_2899_);
                        if v___x_2900_ == 0 {
                            v_lctx_2901_ = crate::leanh::lean_ctor_get(v_mdecl_2882_, 1);
                            v___x_2902_ = l_Lean_LocalDecl_fvarId(v_val_2892_);
                            v___x_2903_ = l_Lean_LocalContext_contains(v_lctx_2901_, v___x_2902_);
                            crate::leanh::lean_dec(v___x_2902_);
                            v___y_2894_ = v___x_2903_;
                            state = 1;
                            continue;
                        } else {
                            v___y_2894_ = v___x_2900_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_2886_;
                }
            }
            1 => {
                if v___y_2894_ == 0 {
                    v___x_2895_ = l_Lean_LocalDecl_userName(v_val_2892_);
                    v___x_2896_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2896_, 0, v___x_2895_);
                    crate::leanh::lean_ctor_set(v___x_2896_, 1, v_b_2886_);
                    v_i_2884_ = v___x_2889_;
                    v_b_2886_ = v___x_2896_;
                    state = 0;
                    continue;
                } else {
                    v_i_2884_ = v___x_2889_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2___boxed(
    mut v_lctxInitIndices_2904_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2905_: *mut crate::leanh::LeanObject,
    mut v_as_2906_: *mut crate::leanh::LeanObject,
    mut v_i_2907_: *mut crate::leanh::LeanObject,
    mut v_stop_2908_: *mut crate::leanh::LeanObject,
    mut v_b_2909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2910_: usize = 0;
    let mut v_stop_boxed_2911_: usize = 0;
    let mut v_res_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2910_ = crate::leanh::lean_unbox_usize(v_i_2907_);
    crate::leanh::lean_dec(v_i_2907_);
    v_stop_boxed_2911_ = crate::leanh::lean_unbox_usize(v_stop_2908_);
    crate::leanh::lean_dec(v_stop_2908_);
    v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_2904_, v_mdecl_2905_, v_as_2906_, v_i_boxed_2910_, v_stop_boxed_2911_, v_b_2909_);
    crate::leanh::lean_dec_ref(v_as_2906_);
    crate::leanh::lean_dec_ref(v_mdecl_2905_);
    crate::leanh::lean_dec(v_lctxInitIndices_2904_);
    return v_res_2912_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(
    mut v_lctxInitIndices_2913_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2914_: *mut crate::leanh::LeanObject,
    mut v_x_2915_: *mut crate::leanh::LeanObject,
    mut v_x_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2915_) == 0 {
        let mut v_cs_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2920_: u8 = 0;
        v_cs_2917_ = crate::leanh::lean_ctor_get(v_x_2915_, 0);
        v___x_2918_ = lean_array_get_size(v_cs_2917_);
        v___x_2919_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2920_ = lean_nat_dec_lt(v___x_2919_, v___x_2918_);
        if v___x_2920_ == 0 {
            return v_x_2916_;
        } else {
            let mut v___x_2921_: usize = 0;
            let mut v___x_2922_: usize = 0;
            let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2921_ = lean_usize_of_nat(v___x_2918_);
            v___x_2922_ = 0usize;
            v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_2913_, v_mdecl_2914_, v_cs_2917_, v___x_2921_, v___x_2922_, v_x_2916_);
            return v___x_2923_;
        }
    } else {
        let mut v_vs_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2927_: u8 = 0;
        v_vs_2924_ = crate::leanh::lean_ctor_get(v_x_2915_, 0);
        v___x_2925_ = lean_array_get_size(v_vs_2924_);
        v___x_2926_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2927_ = lean_nat_dec_lt(v___x_2926_, v___x_2925_);
        if v___x_2927_ == 0 {
            return v_x_2916_;
        } else {
            let mut v___x_2928_: usize = 0;
            let mut v___x_2929_: usize = 0;
            let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2928_ = lean_usize_of_nat(v___x_2925_);
            v___x_2929_ = 0usize;
            v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_2913_, v_mdecl_2914_, v_vs_2924_, v___x_2928_, v___x_2929_, v_x_2916_);
            return v___x_2930_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(
    mut v_lctxInitIndices_2931_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2932_: *mut crate::leanh::LeanObject,
    mut v_as_2933_: *mut crate::leanh::LeanObject,
    mut v_i_2934_: usize,
    mut v_stop_2935_: usize,
    mut v_b_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: usize = 0;
    let mut v___x_2939_: usize = 0;
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2937_ = lean_usize_dec_eq(v_i_2934_, v_stop_2935_);
                if v___x_2937_ == 0 {
                    v___x_2938_ = 1usize;
                    v___x_2939_ = lean_usize_sub(v_i_2934_, v___x_2938_);
                    v___x_2940_ = lean_array_uget_borrowed(v_as_2933_, v___x_2939_);
                    v___x_2941_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_2931_, v_mdecl_2932_, v___x_2940_, v_b_2936_);
                    v_i_2934_ = v___x_2939_;
                    v_b_2936_ = v___x_2941_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2936_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_lctxInitIndices_2943_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2944_: *mut crate::leanh::LeanObject,
    mut v_as_2945_: *mut crate::leanh::LeanObject,
    mut v_i_2946_: *mut crate::leanh::LeanObject,
    mut v_stop_2947_: *mut crate::leanh::LeanObject,
    mut v_b_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2949_: usize = 0;
    let mut v_stop_boxed_2950_: usize = 0;
    let mut v_res_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2949_ = crate::leanh::lean_unbox_usize(v_i_2946_);
    crate::leanh::lean_dec(v_i_2946_);
    v_stop_boxed_2950_ = crate::leanh::lean_unbox_usize(v_stop_2947_);
    crate::leanh::lean_dec(v_stop_2947_);
    v_res_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_2943_, v_mdecl_2944_, v_as_2945_, v_i_boxed_2949_, v_stop_boxed_2950_, v_b_2948_);
    crate::leanh::lean_dec_ref(v_as_2945_);
    crate::leanh::lean_dec_ref(v_mdecl_2944_);
    crate::leanh::lean_dec(v_lctxInitIndices_2943_);
    return v_res_2951_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1___boxed(
    mut v_lctxInitIndices_2952_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2953_: *mut crate::leanh::LeanObject,
    mut v_x_2954_: *mut crate::leanh::LeanObject,
    mut v_x_2955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2956_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_2952_, v_mdecl_2953_, v_x_2954_, v_x_2955_);
    crate::leanh::lean_dec_ref(v_x_2954_);
    crate::leanh::lean_dec_ref(v_mdecl_2953_);
    crate::leanh::lean_dec(v_lctxInitIndices_2952_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(
    mut v_lctxInitIndices_2957_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2958_: *mut crate::leanh::LeanObject,
    mut v_t_2959_: *mut crate::leanh::LeanObject,
    mut v_init_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    v_root_2961_ = crate::leanh::lean_ctor_get(v_t_2959_, 0);
    v_tail_2962_ = crate::leanh::lean_ctor_get(v_t_2959_, 1);
    v___x_2963_ = lean_array_get_size(v_tail_2962_);
    v___x_2964_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2965_ = lean_nat_dec_lt(v___x_2964_, v___x_2963_);
    if v___x_2965_ == 0 {
        let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2966_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_2957_, v_mdecl_2958_, v_root_2961_, v_init_2960_);
        return v___x_2966_;
    } else {
        let mut v___x_2967_: usize = 0;
        let mut v___x_2968_: usize = 0;
        let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2967_ = lean_usize_of_nat(v___x_2963_);
        v___x_2968_ = 0usize;
        v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_2957_, v_mdecl_2958_, v_tail_2962_, v___x_2967_, v___x_2968_, v_init_2960_);
        v___x_2970_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_2957_, v_mdecl_2958_, v_root_2961_, v___x_2969_);
        return v___x_2970_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0___boxed(
    mut v_lctxInitIndices_2971_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2972_: *mut crate::leanh::LeanObject,
    mut v_t_2973_: *mut crate::leanh::LeanObject,
    mut v_init_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2975_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_2971_, v_mdecl_2972_, v_t_2973_, v_init_2974_);
    crate::leanh::lean_dec_ref(v_t_2973_);
    crate::leanh::lean_dec_ref(v_mdecl_2972_);
    crate::leanh::lean_dec(v_lctxInitIndices_2971_);
    return v_res_2975_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(
    mut v_lctxInitIndices_2976_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2977_: *mut crate::leanh::LeanObject,
    mut v_lctx_2978_: *mut crate::leanh::LeanObject,
    mut v_init_2979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_2980_ = crate::leanh::lean_ctor_get(v_lctx_2978_, 1);
    v___x_2981_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_2976_, v_mdecl_2977_, v_decls_2980_, v_init_2979_);
    return v___x_2981_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0___boxed(
    mut v_lctxInitIndices_2982_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2983_: *mut crate::leanh::LeanObject,
    mut v_lctx_2984_: *mut crate::leanh::LeanObject,
    mut v_init_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2986_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_2982_, v_mdecl_2983_, v_lctx_2984_, v_init_2985_);
    crate::leanh::lean_dec_ref(v_lctx_2984_);
    crate::leanh::lean_dec_ref(v_mdecl_2983_);
    crate::leanh::lean_dec(v_lctxInitIndices_2982_);
    return v_res_2986_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(
    mut v_lctxInitIndices_2991_: *mut crate::leanh::LeanObject,
    mut v_mdecl_2992_: *mut crate::leanh::LeanObject,
    mut v_a_2993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    v_lctx_2995_ = crate::leanh::lean_ctor_get(v_a_2993_, 2);
    v___x_2996_ = crate::leanh::lean_box(0);
    v___x_2997_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_2991_, v_mdecl_2992_, v_lctx_2995_, v___x_2996_);
    v___x_2998_ = l_List_isEmpty___redArg(v___x_2997_);
    if v___x_2998_ == 0 {
        let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2999_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0;
        v___x_3000_ = l_List_lengthTR___redArg(v___x_2997_);
        v___x_3001_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1;
        v___x_3002_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2;
        v___x_3003_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_3000_, v___x_3001_, v___x_3002_);
        crate::leanh::lean_dec(v___x_3000_);
        v___x_3004_ = lean_string_append(v___x_2999_, v___x_3003_);
        crate::leanh::lean_dec_ref(v___x_3003_);
        v___x_3005_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3;
        v___x_3006_ = lean_string_append(v___x_3004_, v___x_3005_);
        v___x_3007_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_2997_);
        v___x_3008_ = lean_string_append(v___x_3006_, v___x_3007_);
        crate::leanh::lean_dec_ref(v___x_3007_);
        v___x_3009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3009_, 0, v___x_3008_);
        return v___x_3009_;
    } else {
        let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2997_);
        v___x_3010_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4;
        v___x_3011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3011_, 0, v___x_3010_);
        return v___x_3011_;
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___boxed(
    mut v_lctxInitIndices_3012_: *mut crate::leanh::LeanObject,
    mut v_mdecl_3013_: *mut crate::leanh::LeanObject,
    mut v_a_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3016_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_3012_, v_mdecl_3013_, v_a_3014_);
    crate::leanh::lean_dec_ref(v_a_3014_);
    crate::leanh::lean_dec_ref(v_mdecl_3013_);
    crate::leanh::lean_dec(v_lctxInitIndices_3012_);
    return v_res_3016_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(
    mut v_lctxInitIndices_3017_: *mut crate::leanh::LeanObject,
    mut v_mdecl_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_3017_, v_mdecl_3018_, v_a_3019_);
    return v___x_3024_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___boxed(
    mut v_lctxInitIndices_3025_: *mut crate::leanh::LeanObject,
    mut v_mdecl_3026_: *mut crate::leanh::LeanObject,
    mut v_a_3027_: *mut crate::leanh::LeanObject,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3032_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(v_lctxInitIndices_3025_, v_mdecl_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
    crate::leanh::lean_dec(v_a_3030_);
    crate::leanh::lean_dec_ref(v_a_3029_);
    crate::leanh::lean_dec(v_a_3028_);
    crate::leanh::lean_dec_ref(v_a_3027_);
    crate::leanh::lean_dec_ref(v_mdecl_3026_);
    crate::leanh::lean_dec(v_lctxInitIndices_3025_);
    return v_res_3032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(
    mut v_sz_3033_: usize,
    mut v_i_3034_: usize,
    mut v_bs_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: usize = 0;
    let mut v___x_3049_: usize = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3041_ = lean_usize_dec_lt(v_i_3034_, v_sz_3033_);
                if v___x_3041_ == 0 {
                    v___x_3042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3042_, 0, v_bs_3035_);
                    return v___x_3042_;
                } else {
                    v_v_3043_ = lean_array_uget(v_bs_3035_, v_i_3034_);
                    v___x_3044_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3045_ = lean_array_uset(v_bs_3035_, v_i_3034_, v___x_3044_);
                    v___x_3052_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_v_3043_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
                    if crate::leanh::lean_obj_tag(v___x_3052_) == 0 {
                        v_a_3053_ = crate::leanh::lean_ctor_get(v___x_3052_, 0);
                        crate::leanh::lean_inc(v_a_3053_);
                        crate::leanh::lean_dec_ref_known(v___x_3052_, 1);
                        v___x_3054_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_3053_);
                        crate::leanh::lean_dec(v_a_3053_);
                        v_a_3047_ = v___x_3054_;
                        state = 1;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_3052_) == 0 {
                            v_a_3055_ = crate::leanh::lean_ctor_get(v___x_3052_, 0);
                            crate::leanh::lean_inc(v_a_3055_);
                            crate::leanh::lean_dec_ref_known(v___x_3052_, 1);
                            v_a_3047_ = v_a_3055_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_bs_x27_3045_);
                            v_a_3056_ = crate::leanh::lean_ctor_get(v___x_3052_, 0);
                            v_isSharedCheck_3063_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3052_)) as u8;
                            if v_isSharedCheck_3063_ == 0 {
                                v___x_3058_ = v___x_3052_;
                                v_isShared_3059_ = v_isSharedCheck_3063_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3056_);
                                crate::leanh::lean_dec(v___x_3052_);
                                v___x_3058_ = crate::leanh::lean_box(0);
                                v_isShared_3059_ = v_isSharedCheck_3063_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3048_ = 1usize;
                v___x_3049_ = lean_usize_add(v_i_3034_, v___x_3048_);
                v___x_3050_ = lean_array_uset(v_bs_x27_3045_, v_i_3034_, v_a_3047_);
                v_i_3034_ = v___x_3049_;
                v_bs_3035_ = v___x_3050_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3059_ == 0 {
                    v___x_3061_ = v___x_3058_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
                    v___x_3061_ = v_reuseFailAlloc_3062_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0___boxed(
    mut v_sz_3064_: *mut crate::leanh::LeanObject,
    mut v_i_3065_: *mut crate::leanh::LeanObject,
    mut v_bs_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
    mut v___y_3069_: *mut crate::leanh::LeanObject,
    mut v___y_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3072_: usize = 0;
    let mut v_i_boxed_3073_: usize = 0;
    let mut v_res_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3072_ = crate::leanh::lean_unbox_usize(v_sz_3064_);
    crate::leanh::lean_dec(v_sz_3064_);
    v_i_boxed_3073_ = crate::leanh::lean_unbox_usize(v_i_3065_);
    crate::leanh::lean_dec(v_i_3065_);
    v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_boxed_3072_, v_i_boxed_3073_, v_bs_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
    crate::leanh::lean_dec(v___y_3070_);
    crate::leanh::lean_dec_ref(v___y_3069_);
    crate::leanh::lean_dec(v___y_3068_);
    crate::leanh::lean_dec_ref(v___y_3067_);
    return v_res_3074_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(
    mut v___x_3077_: *mut crate::leanh::LeanObject,
    mut v_as_3078_: *mut crate::leanh::LeanObject,
    mut v_i_3079_: usize,
    mut v_stop_3080_: usize,
    mut v_b_3081_: *mut crate::leanh::LeanObject,
    mut v___y_3082_: *mut crate::leanh::LeanObject,
    mut v___y_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: usize = 0;
    let mut v___x_3090_: usize = 0;
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3103_: u8 = 0;
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3107_: u8 = 0;
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = lean_usize_dec_eq(v_i_3079_, v_stop_3080_);
                if v___x_3092_ == 0 {
                    v___x_3093_ = lean_array_uget_borrowed(v_as_3078_, v_i_3079_);
                    crate::leanh::lean_inc(v___x_3093_);
                    v___x_3094_ = l_Lean_MVarId_getDecl(
                        v___x_3093_,
                        v___y_3082_,
                        v___y_3083_,
                        v___y_3084_,
                        v___y_3085_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3094_) == 0 {
                        v_a_3095_ = crate::leanh::lean_ctor_get(v___x_3094_, 0);
                        crate::leanh::lean_inc(v_a_3095_);
                        crate::leanh::lean_dec_ref_known(v___x_3094_, 1);
                        v_lctx_3096_ = crate::leanh::lean_ctor_get(v_a_3095_, 1);
                        crate::leanh::lean_inc_ref(v_lctx_3096_);
                        crate::leanh::lean_dec(v_a_3095_);
                        v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0;
                        v___x_3098_ = l_Lean_LocalContext_isSubPrefixOf(
                            v_lctx_3096_,
                            v___x_3077_,
                            v___x_3097_,
                        );
                        crate::leanh::lean_dec_ref(v_lctx_3096_);
                        if v___x_3098_ == 0 {
                            crate::leanh::lean_inc(v___x_3093_);
                            v___x_3099_ = lean_array_push(v_b_3081_, v___x_3093_);
                            v_a_3088_ = v___x_3099_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3088_ = v_b_3081_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3081_);
                        v_a_3100_ = crate::leanh::lean_ctor_get(v___x_3094_, 0);
                        v_isSharedCheck_3107_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3094_)) as u8;
                        if v_isSharedCheck_3107_ == 0 {
                            v___x_3102_ = v___x_3094_;
                            v_isShared_3103_ = v_isSharedCheck_3107_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3100_);
                            crate::leanh::lean_dec(v___x_3094_);
                            v___x_3102_ = crate::leanh::lean_box(0);
                            v_isShared_3103_ = v_isSharedCheck_3107_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3108_, 0, v_b_3081_);
                    return v___x_3108_;
                }
            }
            1 => {
                v___x_3089_ = 1usize;
                v___x_3090_ = lean_usize_add(v_i_3079_, v___x_3089_);
                v_i_3079_ = v___x_3090_;
                v_b_3081_ = v_a_3088_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3103_ == 0 {
                    v___x_3105_ = v___x_3102_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
                    v___x_3105_ = v_reuseFailAlloc_3106_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___boxed(
    mut v___x_3109_: *mut crate::leanh::LeanObject,
    mut v_as_3110_: *mut crate::leanh::LeanObject,
    mut v_i_3111_: *mut crate::leanh::LeanObject,
    mut v_stop_3112_: *mut crate::leanh::LeanObject,
    mut v_b_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3119_: usize = 0;
    let mut v_stop_boxed_3120_: usize = 0;
    let mut v_res_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3119_ = crate::leanh::lean_unbox_usize(v_i_3111_);
    crate::leanh::lean_dec(v_i_3111_);
    v_stop_boxed_3120_ = crate::leanh::lean_unbox_usize(v_stop_3112_);
    crate::leanh::lean_dec(v_stop_3112_);
    v_res_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v___x_3109_, v_as_3110_, v_i_boxed_3119_, v_stop_boxed_3120_, v_b_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
    crate::leanh::lean_dec(v___y_3117_);
    crate::leanh::lean_dec_ref(v___y_3116_);
    crate::leanh::lean_dec(v___y_3115_);
    crate::leanh::lean_dec_ref(v___y_3114_);
    crate::leanh::lean_dec_ref(v_as_3110_);
    crate::leanh::lean_dec_ref(v___x_3109_);
    return v_res_3121_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(
    mut v_e_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
    mut v_a_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_awaitingMVars_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: u8 = 0;
    let mut v_sz_3143_: usize = 0;
    let mut v___x_3144_: usize = 0;
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v_a_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u8 = 0;
    let mut v___y_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v_lctx_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: usize = 0;
    let mut v___x_3201_: usize = 0;
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: usize = 0;
    let mut v___x_3204_: usize = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3176_ = l_Lean_Meta_getMVarsNoDelayed(
                    v_e_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_,
                );
                if crate::leanh::lean_obj_tag(v___x_3176_) == 0 {
                    v_a_3177_ = crate::leanh::lean_ctor_get(v___x_3176_, 0);
                    crate::leanh::lean_inc(v_a_3177_);
                    crate::leanh::lean_dec_ref_known(v___x_3176_, 1);
                    v___x_3194_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3195_ = lean_array_get_size(v_a_3177_);
                    v___x_3196_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4;
                    v___x_3197_ = lean_nat_dec_lt(v___x_3194_, v___x_3195_);
                    if v___x_3197_ == 0 {
                        v_a_3179_ = v___x_3196_;
                        state = 6;
                        continue;
                    } else {
                        v_lctx_3198_ = crate::leanh::lean_ctor_get(v_a_3129_, 2);
                        v___x_3199_ = lean_nat_dec_le(v___x_3195_, v___x_3195_);
                        if v___x_3199_ == 0 {
                            if v___x_3197_ == 0 {
                                v_a_3179_ = v___x_3196_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3200_ = 0usize;
                                v___x_3201_ = lean_usize_of_nat(v___x_3195_);
                                v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_3198_, v_a_3177_, v___x_3200_, v___x_3201_, v___x_3196_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
                                v___y_3184_ = v___x_3202_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_3203_ = 0usize;
                            v___x_3204_ = lean_usize_of_nat(v___x_3195_);
                            v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v_lctx_3198_, v_a_3177_, v___x_3203_, v___x_3204_, v___x_3196_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
                            v___y_3184_ = v___x_3205_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_3206_ = crate::leanh::lean_ctor_get(v___x_3176_, 0);
                    v_isSharedCheck_3213_ = (!crate::leanh::lean_is_exclusive(v___x_3176_)) as u8;
                    if v_isSharedCheck_3213_ == 0 {
                        v___x_3208_ = v___x_3176_;
                        v_isShared_3209_ = v_isSharedCheck_3213_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3206_);
                        crate::leanh::lean_dec(v___x_3176_);
                        v___x_3208_ = crate::leanh::lean_box(0);
                        v_isShared_3209_ = v_isSharedCheck_3213_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3140_ = lean_array_get_size(v_awaitingMVars_3135_);
                v___x_3141_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3142_ = lean_nat_dec_eq(v___x_3140_, v___x_3141_);
                if v___x_3142_ == 0 {
                    v_sz_3143_ = lean_array_size(v_awaitingMVars_3135_);
                    v___x_3144_ = 0usize;
                    v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_3143_, v___x_3144_, v_awaitingMVars_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
                    if crate::leanh::lean_obj_tag(v___x_3145_) == 0 {
                        v_a_3146_ = crate::leanh::lean_ctor_get(v___x_3145_, 0);
                        v_isSharedCheck_3165_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3145_)) as u8;
                        if v_isSharedCheck_3165_ == 0 {
                            v___x_3148_ = v___x_3145_;
                            v_isShared_3149_ = v_isSharedCheck_3165_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3146_);
                            crate::leanh::lean_dec(v___x_3145_);
                            v___x_3148_ = crate::leanh::lean_box(0);
                            v_isShared_3149_ = v_isSharedCheck_3165_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3166_ = crate::leanh::lean_ctor_get(v___x_3145_, 0);
                        v_isSharedCheck_3173_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3145_)) as u8;
                        if v_isSharedCheck_3173_ == 0 {
                            v___x_3168_ = v___x_3145_;
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3166_);
                            crate::leanh::lean_dec(v___x_3145_);
                            v___x_3168_ = crate::leanh::lean_box(0);
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_awaitingMVars_3135_);
                    v___x_3174_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4;
                    v___x_3175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3174_);
                    return v___x_3175_;
                }
            }
            2 => {
                v___x_3150_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0;
                v___x_3151_ = lean_array_get_size(v_a_3146_);
                v___x_3152_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1;
                v___x_3153_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2;
                v___x_3154_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_3151_, v___x_3152_, v___x_3153_);
                v___x_3155_ = lean_string_append(v___x_3150_, v___x_3154_);
                crate::leanh::lean_dec_ref(v___x_3154_);
                v___x_3156_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3;
                v___x_3157_ = lean_string_append(v___x_3155_, v___x_3156_);
                v___x_3158_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0;
                v___x_3159_ = lean_array_to_list(v_a_3146_);
                v___x_3160_ = l_String_intercalate(v___x_3158_, v___x_3159_);
                v___x_3161_ = lean_string_append(v___x_3157_, v___x_3160_);
                crate::leanh::lean_dec_ref(v___x_3160_);
                if v_isShared_3149_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3148_, 0, v___x_3161_);
                    v___x_3163_ = v___x_3148_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
                    v___x_3163_ = v_reuseFailAlloc_3164_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3163_;
            }
            4 => {
                if v_isShared_3169_ == 0 {
                    v___x_3171_ = v___x_3168_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
                    v___x_3171_ = v_reuseFailAlloc_3172_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3171_;
            }
            6 => {
                v___x_3180_ = lean_array_get_size(v_a_3179_);
                v___x_3181_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3182_ = lean_nat_dec_eq(v___x_3180_, v___x_3181_);
                if v___x_3182_ == 0 {
                    crate::leanh::lean_dec(v_a_3177_);
                    v_awaitingMVars_3135_ = v_a_3179_;
                    v___y_3136_ = v_a_3129_;
                    v___y_3137_ = v_a_3130_;
                    v___y_3138_ = v_a_3131_;
                    v___y_3139_ = v_a_3132_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_3179_);
                    v_awaitingMVars_3135_ = v_a_3177_;
                    v___y_3136_ = v_a_3129_;
                    v___y_3137_ = v_a_3130_;
                    v___y_3138_ = v_a_3131_;
                    v___y_3139_ = v_a_3132_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_3184_) == 0 {
                    v_a_3185_ = crate::leanh::lean_ctor_get(v___y_3184_, 0);
                    crate::leanh::lean_inc(v_a_3185_);
                    crate::leanh::lean_dec_ref_known(v___y_3184_, 1);
                    v_a_3179_ = v_a_3185_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3177_);
                    v_a_3186_ = crate::leanh::lean_ctor_get(v___y_3184_, 0);
                    v_isSharedCheck_3193_ = (!crate::leanh::lean_is_exclusive(v___y_3184_)) as u8;
                    if v_isSharedCheck_3193_ == 0 {
                        v___x_3188_ = v___y_3184_;
                        v_isShared_3189_ = v_isSharedCheck_3193_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3186_);
                        crate::leanh::lean_dec(v___y_3184_);
                        v___x_3188_ = crate::leanh::lean_box(0);
                        v_isShared_3189_ = v_isSharedCheck_3193_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_3189_ == 0 {
                    v___x_3191_ = v___x_3188_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
                    v___x_3191_ = v_reuseFailAlloc_3192_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3191_;
            }
            10 => {
                if v_isShared_3209_ == 0 {
                    v___x_3211_ = v___x_3208_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
                    v___x_3211_ = v_reuseFailAlloc_3212_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___boxed(
    mut v_e_3214_: *mut crate::leanh::LeanObject,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
    mut v_a_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3220_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_e_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
    crate::leanh::lean_dec(v_a_3218_);
    crate::leanh::lean_dec_ref(v_a_3217_);
    crate::leanh::lean_dec(v_a_3216_);
    crate::leanh::lean_dec_ref(v_a_3215_);
    return v_res_3220_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(
    mut v_mvarId_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3224_ = lean_st_ref_get(v___y_3222_);
    v_mctx_3225_ = crate::leanh::lean_ctor_get(v___x_3224_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3225_);
    crate::leanh::lean_dec(v___x_3224_);
    v_decl_3226_ = l_Lean_MetavarContext_getDecl(v_mctx_3225_, v_mvarId_3221_);
    v_depth_3227_ = crate::leanh::lean_ctor_get(v_decl_3226_, 3);
    crate::leanh::lean_inc(v_depth_3227_);
    crate::leanh::lean_dec_ref(v_decl_3226_);
    v_depth_3228_ = crate::leanh::lean_ctor_get(v_mctx_3225_, 0);
    crate::leanh::lean_inc(v_depth_3228_);
    crate::leanh::lean_dec_ref(v_mctx_3225_);
    v___x_3229_ = lean_nat_dec_eq(v_depth_3227_, v_depth_3228_);
    crate::leanh::lean_dec(v_depth_3228_);
    crate::leanh::lean_dec(v_depth_3227_);
    v___x_3230_ = crate::leanh::lean_box((v___x_3229_) as usize);
    v___x_3231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3231_, 0, v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg___boxed(
    mut v_mvarId_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3235_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_3232_, v___y_3233_);
    crate::leanh::lean_dec(v___y_3233_);
    return v_res_3235_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(
    mut v_mvarId_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_3236_, v___y_3238_);
    return v___x_3242_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___boxed(
    mut v_mvarId_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3249_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(v_mvarId_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
    crate::leanh::lean_dec(v___y_3247_);
    crate::leanh::lean_dec_ref(v___y_3246_);
    crate::leanh::lean_dec(v___y_3245_);
    crate::leanh::lean_dec_ref(v___y_3244_);
    return v_res_3249_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(
    mut v_mvarId_3263_: *mut crate::leanh::LeanObject,
    mut v_lctxInitIndices_3264_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3265_: u8,
    mut v_a_3266_: *mut crate::leanh::LeanObject,
    mut v_a_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v_val_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v___y_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delayedExpl_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v_val_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v_a_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v_a_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3348_: u8 = 0;
    let mut v_a_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3352_: u8 = 0;
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3356_: u8 = 0;
    let mut v_userName_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3359_: u8 = 0;
    let mut v_msg_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v_msg_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3407_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v_mctx_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: u8 = 0;
    let mut v_reuseFailAlloc_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_a_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3271_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarId_3263_, v_a_3267_);
                if crate::leanh::lean_obj_tag(v___x_3271_) == 0 {
                    v_a_3272_ = crate::leanh::lean_ctor_get(v___x_3271_, 0);
                    v_isSharedCheck_3432_ = (!crate::leanh::lean_is_exclusive(v___x_3271_)) as u8;
                    if v_isSharedCheck_3432_ == 0 {
                        v___x_3274_ = v___x_3271_;
                        v_isShared_3275_ = v_isSharedCheck_3432_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3272_);
                        crate::leanh::lean_dec(v___x_3271_);
                        v___x_3274_ = crate::leanh::lean_box(0);
                        v_isShared_3275_ = v_isSharedCheck_3432_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3263_);
                    v_a_3433_ = crate::leanh::lean_ctor_get(v___x_3271_, 0);
                    v_isSharedCheck_3440_ = (!crate::leanh::lean_is_exclusive(v___x_3271_)) as u8;
                    if v_isSharedCheck_3440_ == 0 {
                        v___x_3435_ = v___x_3271_;
                        v_isShared_3436_ = v_isSharedCheck_3440_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3433_);
                        crate::leanh::lean_dec(v___x_3271_);
                        v___x_3435_ = crate::leanh::lean_box(0);
                        v_isShared_3436_ = v_isSharedCheck_3440_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3272_) == 1 {
                    crate::leanh::lean_del_object(v___x_3274_);
                    v_val_3276_ = crate::leanh::lean_ctor_get(v_a_3272_, 0);
                    v_isSharedCheck_3427_ = (!crate::leanh::lean_is_exclusive(v_a_3272_)) as u8;
                    if v_isSharedCheck_3427_ == 0 {
                        v___x_3278_ = v_a_3272_;
                        v_isShared_3279_ = v_isSharedCheck_3427_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3276_);
                        crate::leanh::lean_dec(v_a_3272_);
                        v___x_3278_ = crate::leanh::lean_box(0);
                        v_isShared_3279_ = v_isSharedCheck_3427_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3272_);
                    crate::leanh::lean_dec(v_mvarId_3263_);
                    v___x_3428_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12;
                    if v_isShared_3275_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3274_, 0, v___x_3428_);
                        v___x_3430_ = v___x_3274_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
                        v___x_3430_ = v_reuseFailAlloc_3431_;
                        state = 23;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3293_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_3263_, v_a_3267_);
                v_a_3294_ = crate::leanh::lean_ctor_get(v___x_3293_, 0);
                crate::leanh::lean_inc(v_a_3294_);
                crate::leanh::lean_dec_ref(v___x_3293_);
                v_delayedExpl_3295_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0;
                if crate::leanh::lean_obj_tag(v_a_3294_) == 1 {
                    crate::leanh::lean_del_object(v___x_3278_);
                    crate::leanh::lean_dec(v_val_3276_);
                    crate::leanh::lean_dec(v_mvarId_3263_);
                    v_val_3296_ = crate::leanh::lean_ctor_get(v_a_3294_, 0);
                    crate::leanh::lean_inc(v_val_3296_);
                    crate::leanh::lean_dec_ref_known(v_a_3294_, 1);
                    v_mvarIdPending_3297_ = crate::leanh::lean_ctor_get(v_val_3296_, 1);
                    crate::leanh::lean_inc(v_mvarIdPending_3297_);
                    crate::leanh::lean_dec(v_val_3296_);
                    v___x_3298_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(
                        v_mvarIdPending_3297_,
                        v_a_3266_,
                        v_a_3267_,
                        v_a_3268_,
                        v_a_3269_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3298_) == 0 {
                        v_a_3299_ = crate::leanh::lean_ctor_get(v___x_3298_, 0);
                        crate::leanh::lean_inc(v_a_3299_);
                        crate::leanh::lean_dec_ref_known(v___x_3298_, 1);
                        v___x_3300_ = l_Lean_MVarId_findDecl_x3f___redArg(v_a_3299_, v_a_3267_);
                        if crate::leanh::lean_obj_tag(v___x_3300_) == 0 {
                            v_a_3301_ = crate::leanh::lean_ctor_get(v___x_3300_, 0);
                            v_isSharedCheck_3340_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3300_)) as u8;
                            if v_isSharedCheck_3340_ == 0 {
                                v___x_3303_ = v___x_3300_;
                                v_isShared_3304_ = v_isSharedCheck_3340_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3301_);
                                crate::leanh::lean_dec(v___x_3300_);
                                v___x_3303_ = crate::leanh::lean_box(0);
                                v_isShared_3304_ = v_isSharedCheck_3340_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3299_);
                            v_a_3341_ = crate::leanh::lean_ctor_get(v___x_3300_, 0);
                            v_isSharedCheck_3348_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3300_)) as u8;
                            if v_isSharedCheck_3348_ == 0 {
                                v___x_3343_ = v___x_3300_;
                                v_isShared_3344_ = v_isSharedCheck_3348_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3341_);
                                crate::leanh::lean_dec(v___x_3300_);
                                v___x_3343_ = crate::leanh::lean_box(0);
                                v_isShared_3344_ = v_isSharedCheck_3348_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        v_a_3349_ = crate::leanh::lean_ctor_get(v___x_3298_, 0);
                        v_isSharedCheck_3356_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3298_)) as u8;
                        if v_isSharedCheck_3356_ == 0 {
                            v___x_3351_ = v___x_3298_;
                            v_isShared_3352_ = v_isSharedCheck_3356_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3349_);
                            crate::leanh::lean_dec(v___x_3298_);
                            v___x_3351_ = crate::leanh::lean_box(0);
                            v_isShared_3352_ = v_isSharedCheck_3356_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3294_);
                    v_userName_3357_ = crate::leanh::lean_ctor_get(v_val_3276_, 0);
                    v_lctx_3358_ = crate::leanh::lean_ctor_get(v_val_3276_, 1);
                    v_kind_3359_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_3276_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    );
                    match v_kind_3359_ {
                        0 => {
                            v___x_3424_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9;
                            v_msg_3411_ = v___x_3424_;
                            v___y_3412_ = v_a_3266_;
                            v___y_3413_ = v_a_3267_;
                            v___y_3414_ = v_a_3268_;
                            v___y_3415_ = v_a_3269_;
                            state = 21;
                            continue;
                        }
                        1 => {
                            v___x_3425_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10;
                            v_msg_3411_ = v___x_3425_;
                            v___y_3412_ = v_a_3266_;
                            v___y_3413_ = v_a_3267_;
                            v___y_3414_ = v_a_3268_;
                            v___y_3415_ = v_a_3269_;
                            state = 21;
                            continue;
                        }
                        _ => {
                            v___x_3426_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11;
                            v_msg_3411_ = v___x_3426_;
                            v___y_3412_ = v_a_3266_;
                            v___y_3413_ = v_a_3267_;
                            v___y_3414_ = v_a_3268_;
                            v___y_3415_ = v_a_3269_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_3283_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_3264_, v_val_3276_, v___y_3281_);
                crate::leanh::lean_dec(v_val_3276_);
                v_a_3284_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                v_isSharedCheck_3292_ = (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                if v_isSharedCheck_3292_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    v_isShared_3287_ = v_isSharedCheck_3292_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3284_);
                    crate::leanh::lean_dec(v___x_3283_);
                    v___x_3286_ = crate::leanh::lean_box(0);
                    v_isShared_3287_ = v_isSharedCheck_3292_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3288_ = lean_string_append(v___y_3282_, v_a_3284_);
                crate::leanh::lean_dec(v_a_3284_);
                if v_isShared_3287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3286_, 0, v___x_3288_);
                    v___x_3290_ = v___x_3286_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
                    v___x_3290_ = v_reuseFailAlloc_3291_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3290_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_3301_) == 1 {
                    crate::leanh::lean_del_object(v___x_3303_);
                    v_val_3305_ = crate::leanh::lean_ctor_get(v_a_3301_, 0);
                    crate::leanh::lean_inc(v_val_3305_);
                    crate::leanh::lean_dec_ref_known(v_a_3301_, 1);
                    crate::leanh::lean_inc(v_a_3299_);
                    v___x_3332_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_a_3299_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
                    if crate::leanh::lean_obj_tag(v___x_3332_) == 0 {
                        v_a_3333_ = crate::leanh::lean_ctor_get(v___x_3332_, 0);
                        crate::leanh::lean_inc(v_a_3333_);
                        crate::leanh::lean_dec_ref_known(v___x_3332_, 1);
                        v___x_3334_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_3333_);
                        crate::leanh::lean_dec(v_a_3333_);
                        v_a_3320_ = v___x_3334_;
                        state = 10;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_3332_) == 0 {
                            v_a_3335_ = crate::leanh::lean_ctor_get(v___x_3332_, 0);
                            crate::leanh::lean_inc(v_a_3335_);
                            crate::leanh::lean_dec_ref_known(v___x_3332_, 1);
                            v_a_3320_ = v_a_3335_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_3305_);
                            crate::leanh::lean_dec(v_a_3299_);
                            return v___x_3332_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3301_);
                    crate::leanh::lean_dec(v_a_3299_);
                    v___x_3336_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3;
                    if v_isShared_3304_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3303_, 0, v___x_3336_);
                        v___x_3338_ = v___x_3303_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
                        v___x_3338_ = v_reuseFailAlloc_3339_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3309_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_3305_, v___y_3308_);
                crate::leanh::lean_dec(v_val_3305_);
                v_a_3310_ = crate::leanh::lean_ctor_get(v___x_3309_, 0);
                v_isSharedCheck_3318_ = (!crate::leanh::lean_is_exclusive(v___x_3309_)) as u8;
                if v_isSharedCheck_3318_ == 0 {
                    v___x_3312_ = v___x_3309_;
                    v_isShared_3313_ = v_isSharedCheck_3318_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3310_);
                    crate::leanh::lean_dec(v___x_3309_);
                    v___x_3312_ = crate::leanh::lean_box(0);
                    v_isShared_3313_ = v_isSharedCheck_3318_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3314_ = lean_string_append(v_msg_3307_, v_a_3310_);
                crate::leanh::lean_dec(v_a_3310_);
                if v_isShared_3313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3314_);
                    v___x_3316_ = v___x_3312_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
                    v___x_3316_ = v_reuseFailAlloc_3317_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3316_;
            }
            10 => {
                v___x_3321_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_a_3299_, v_a_3267_);
                crate::leanh::lean_dec(v_a_3299_);
                v_a_3322_ = crate::leanh::lean_ctor_get(v___x_3321_, 0);
                crate::leanh::lean_inc(v_a_3322_);
                crate::leanh::lean_dec_ref(v___x_3321_);
                v___x_3323_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1;
                v___x_3324_ = lean_string_append(v___x_3323_, v_a_3320_);
                crate::leanh::lean_dec_ref(v_a_3320_);
                v___x_3325_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2;
                v___x_3326_ = lean_string_append(v___x_3324_, v___x_3325_);
                v___x_3327_ = lean_string_append(v___x_3326_, v_delayedExpl_3295_);
                if crate::leanh::lean_obj_tag(v_a_3322_) == 1 {
                    v_val_3328_ = crate::leanh::lean_ctor_get(v_a_3322_, 0);
                    crate::leanh::lean_inc(v_val_3328_);
                    crate::leanh::lean_dec_ref_known(v_a_3322_, 1);
                    v___x_3329_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_3328_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
                    if crate::leanh::lean_obj_tag(v___x_3329_) == 0 {
                        v_a_3330_ = crate::leanh::lean_ctor_get(v___x_3329_, 0);
                        crate::leanh::lean_inc(v_a_3330_);
                        crate::leanh::lean_dec_ref_known(v___x_3329_, 1);
                        v___x_3331_ = lean_string_append(v___x_3327_, v_a_3330_);
                        crate::leanh::lean_dec(v_a_3330_);
                        v_msg_3307_ = v___x_3331_;
                        v___y_3308_ = v_a_3266_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3327_);
                        crate::leanh::lean_dec(v_val_3305_);
                        return v___x_3329_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3322_);
                    v_msg_3307_ = v___x_3327_;
                    v___y_3308_ = v_a_3266_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                return v___x_3338_;
            }
            12 => {
                if v_isShared_3344_ == 0 {
                    v___x_3346_ = v___x_3343_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
                    v___x_3346_ = v_reuseFailAlloc_3347_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3346_;
            }
            14 => {
                if v_isShared_3352_ == 0 {
                    v___x_3354_ = v___x_3351_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3355_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
                    v___x_3354_ = v_reuseFailAlloc_3355_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3354_;
            }
            16 => {
                if v_fromDelayed_3265_ == 0 {
                    v___y_3281_ = v___y_3362_;
                    v___y_3282_ = v_msg_3361_;
                    state = 3;
                    continue;
                } else {
                    v_lctx_3363_ = crate::leanh::lean_ctor_get(v___y_3362_, 2);
                    v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0;
                    v___x_3365_ =
                        l_Lean_LocalContext_isSubPrefixOf(v_lctx_3358_, v_lctx_3363_, v___x_3364_);
                    if v___x_3365_ == 0 {
                        v___x_3366_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_3276_, v___y_3362_);
                        crate::leanh::lean_dec(v_val_3276_);
                        v_a_3367_ = crate::leanh::lean_ctor_get(v___x_3366_, 0);
                        v_isSharedCheck_3375_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3366_)) as u8;
                        if v_isSharedCheck_3375_ == 0 {
                            v___x_3369_ = v___x_3366_;
                            v_isShared_3370_ = v_isSharedCheck_3375_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3367_);
                            crate::leanh::lean_dec(v___x_3366_);
                            v___x_3369_ = crate::leanh::lean_box(0);
                            v_isShared_3370_ = v_isSharedCheck_3375_;
                            state = 17;
                            continue;
                        }
                    } else {
                        v___y_3281_ = v___y_3362_;
                        v___y_3282_ = v_msg_3361_;
                        state = 3;
                        continue;
                    }
                }
            }
            17 => {
                v___x_3371_ = lean_string_append(v_msg_3361_, v_a_3367_);
                crate::leanh::lean_dec(v_a_3367_);
                if v_isShared_3370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3369_, 0, v___x_3371_);
                    v___x_3373_ = v___x_3369_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
                    v___x_3373_ = v_reuseFailAlloc_3374_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3373_;
            }
            19 => {
                v___x_3382_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_3263_, v___y_3379_);
                v_a_3383_ = crate::leanh::lean_ctor_get(v___x_3382_, 0);
                crate::leanh::lean_inc(v_a_3383_);
                crate::leanh::lean_dec_ref(v___x_3382_);
                if crate::leanh::lean_obj_tag(v_a_3383_) == 1 {
                    crate::leanh::lean_dec(v_mvarId_3263_);
                    if v_fromDelayed_3265_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_3383_, 1);
                        v___x_3384_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4;
                        v___x_3385_ = lean_string_append(v_msg_3377_, v___x_3384_);
                        v_msg_3361_ = v___x_3385_;
                        v___y_3362_ = v___y_3378_;
                        state = 16;
                        continue;
                    } else {
                        v_val_3386_ = crate::leanh::lean_ctor_get(v_a_3383_, 0);
                        crate::leanh::lean_inc(v_val_3386_);
                        crate::leanh::lean_dec_ref_known(v_a_3383_, 1);
                        v___x_3387_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_3386_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
                        if crate::leanh::lean_obj_tag(v___x_3387_) == 0 {
                            v_a_3388_ = crate::leanh::lean_ctor_get(v___x_3387_, 0);
                            crate::leanh::lean_inc(v_a_3388_);
                            crate::leanh::lean_dec_ref_known(v___x_3387_, 1);
                            v___x_3389_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5;
                            v___x_3390_ = lean_string_append(v_msg_3377_, v___x_3389_);
                            v___x_3391_ = lean_string_append(v___x_3390_, v_delayedExpl_3295_);
                            v___x_3392_ = lean_string_append(v___x_3391_, v_a_3388_);
                            crate::leanh::lean_dec(v_a_3388_);
                            v_msg_3361_ = v___x_3392_;
                            v___y_3362_ = v___y_3378_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_msg_3377_);
                            crate::leanh::lean_dec(v_val_3276_);
                            return v___x_3387_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3383_);
                    v___x_3393_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_3263_, v___y_3379_);
                    v_a_3394_ = crate::leanh::lean_ctor_get(v___x_3393_, 0);
                    crate::leanh::lean_inc(v_a_3394_);
                    crate::leanh::lean_dec_ref(v___x_3393_);
                    v___x_3395_ = (crate::leanh::lean_unbox(v_a_3394_) as u8);
                    crate::leanh::lean_dec(v_a_3394_);
                    if v___x_3395_ == 0 {
                        v___x_3396_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6;
                        v___x_3397_ = lean_string_append(v_msg_3377_, v___x_3396_);
                        v_msg_3361_ = v___x_3397_;
                        v___y_3362_ = v___y_3378_;
                        state = 16;
                        continue;
                    } else {
                        if v_fromDelayed_3265_ == 0 {
                            v_msg_3361_ = v_msg_3377_;
                            v___y_3362_ = v___y_3378_;
                            state = 16;
                            continue;
                        } else {
                            v___x_3398_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7;
                            v___x_3399_ = lean_string_append(v_msg_3377_, v___x_3398_);
                            v___x_3400_ = lean_string_append(v___x_3399_, v_delayedExpl_3295_);
                            v_msg_3361_ = v___x_3400_;
                            v___y_3362_ = v___y_3378_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            20 => {
                if v___y_3407_ == 0 {
                    v___x_3408_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8;
                    crate::leanh::lean_inc_ref(v___y_3402_);
                    v___x_3409_ = lean_string_append(v___y_3402_, v___x_3408_);
                    v_msg_3377_ = v___x_3409_;
                    v___y_3378_ = v___y_3406_;
                    v___y_3379_ = v___y_3403_;
                    v___y_3380_ = v___y_3405_;
                    v___y_3381_ = v___y_3404_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v___y_3402_);
                    v_msg_3377_ = v___y_3402_;
                    v___y_3378_ = v___y_3406_;
                    v___y_3379_ = v___y_3403_;
                    v___y_3380_ = v___y_3405_;
                    v___y_3381_ = v___y_3404_;
                    state = 19;
                    continue;
                }
            }
            21 => {
                v___x_3416_ = lean_st_ref_get(v___y_3413_);
                v___x_3417_ = l_Lean_Name_isAnonymous(v_userName_3357_);
                if v___x_3417_ == 0 {
                    v_mctx_3418_ = crate::leanh::lean_ctor_get(v___x_3416_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3418_);
                    crate::leanh::lean_dec(v___x_3416_);
                    crate::leanh::lean_inc(v_mvarId_3263_);
                    if v_isShared_3279_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3278_, 0, v_mvarId_3263_);
                        v___x_3420_ = v___x_3278_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_mvarId_3263_);
                        v___x_3420_ = v_reuseFailAlloc_3423_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3416_);
                    crate::leanh::lean_del_object(v___x_3278_);
                    v___y_3402_ = v_msg_3411_;
                    v___y_3403_ = v___y_3413_;
                    v___y_3404_ = v___y_3415_;
                    v___y_3405_ = v___y_3414_;
                    v___y_3406_ = v___y_3412_;
                    v___y_3407_ = v___x_3417_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                v___x_3421_ =
                    l_Lean_MetavarContext_findUserName_x3f(v_mctx_3418_, v_userName_3357_);
                crate::leanh::lean_dec_ref(v_mctx_3418_);
                v___x_3422_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_3420_, v___x_3421_);
                crate::leanh::lean_dec(v___x_3421_);
                crate::leanh::lean_dec_ref(v___x_3420_);
                v___y_3402_ = v_msg_3411_;
                v___y_3403_ = v___y_3413_;
                v___y_3404_ = v___y_3415_;
                v___y_3405_ = v___y_3414_;
                v___y_3406_ = v___y_3412_;
                v___y_3407_ = v___x_3422_;
                state = 20;
                continue;
            }
            23 => {
                return v___x_3430_;
            }
            24 => {
                if v_isShared_3436_ == 0 {
                    v___x_3438_ = v___x_3435_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
                    v___x_3438_ = v_reuseFailAlloc_3439_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed(
    mut v_mvarId_3441_: *mut crate::leanh::LeanObject,
    mut v_lctxInitIndices_3442_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
    mut v_a_3448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromDelayed_boxed_3449_: u8 = 0;
    let mut v_res_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3449_ = (crate::leanh::lean_unbox(v_fromDelayed_3443_) as u8);
    v_res_3450_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(v_mvarId_3441_, v_lctxInitIndices_3442_, v_fromDelayed_boxed_3449_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
    crate::leanh::lean_dec(v_a_3447_);
    crate::leanh::lean_dec_ref(v_a_3446_);
    crate::leanh::lean_dec(v_a_3445_);
    crate::leanh::lean_dec_ref(v_a_3444_);
    crate::leanh::lean_dec(v_lctxInitIndices_3442_);
    return v_res_3450_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(
    mut v_mvarId_3451_: *mut crate::leanh::LeanObject,
    mut v_lctxInitIndices_3452_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3453_: u8,
    mut v_ppCtx_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = crate::leanh::lean_box((v_fromDelayed_3453_) as usize);
    v___x_3457_ = crate::leanh::lean_alloc_closure(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_3457_, 0, v_mvarId_3451_);
    crate::leanh::lean_closure_set(v___x_3457_, 1, v_lctxInitIndices_3452_);
    crate::leanh::lean_closure_set(v___x_3457_, 2, v___x_3456_);
    v___x_3458_ = l_Lean_PPContext_runMetaM___redArg(v_ppCtx_3454_, v___x_3457_);
    return v___x_3458_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed(
    mut v_mvarId_3459_: *mut crate::leanh::LeanObject,
    mut v_lctxInitIndices_3460_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3461_: *mut crate::leanh::LeanObject,
    mut v_ppCtx_3462_: *mut crate::leanh::LeanObject,
    mut v___y_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromDelayed_boxed_3464_: u8 = 0;
    let mut v_res_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3464_ = (crate::leanh::lean_unbox(v_fromDelayed_3461_) as u8);
    v_res_3465_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(
        v_mvarId_3459_,
        v_lctxInitIndices_3460_,
        v_fromDelayed_boxed_3464_,
        v_ppCtx_3462_,
    );
    crate::leanh::lean_dec_ref(v_ppCtx_3462_);
    return v_res_3465_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(
    mut v_mvarId_3466_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3467_: u8,
    mut v_a_3468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctxInitIndices_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctxInitIndices_3470_ = crate::leanh::lean_ctor_get(v_a_3468_, 5);
    v___x_3471_ = crate::leanh::lean_box((v_fromDelayed_3467_) as usize);
    crate::leanh::lean_inc(v_lctxInitIndices_3470_);
    v___f_3472_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3472_, 0, v_mvarId_3466_);
    crate::leanh::lean_closure_set(v___f_3472_, 1, v_lctxInitIndices_3470_);
    crate::leanh::lean_closure_set(v___f_3472_, 2, v___x_3471_);
    v___x_3473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3473_, 0, v___f_3472_);
    return v___x_3473_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___boxed(
    mut v_mvarId_3474_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
    mut v_a_3477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromDelayed_boxed_3478_: u8 = 0;
    let mut v_res_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3478_ = (crate::leanh::lean_unbox(v_fromDelayed_3475_) as u8);
    v_res_3479_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(
        v_mvarId_3474_,
        v_fromDelayed_boxed_3478_,
        v_a_3476_,
    );
    crate::leanh::lean_dec_ref(v_a_3476_);
    return v_res_3479_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(
    mut v_mvarId_3480_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3481_: u8,
    mut v_a_3482_: *mut crate::leanh::LeanObject,
    mut v_a_3483_: *mut crate::leanh::LeanObject,
    mut v_a_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(
        v_mvarId_3480_,
        v_fromDelayed_3481_,
        v_a_3482_,
    );
    return v___x_3489_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___boxed(
    mut v_mvarId_3490_: *mut crate::leanh::LeanObject,
    mut v_fromDelayed_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
    mut v_a_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
    mut v_a_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromDelayed_boxed_3499_: u8 = 0;
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3499_ = (crate::leanh::lean_unbox(v_fromDelayed_3491_) as u8);
    v_res_3500_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(
        v_mvarId_3490_,
        v_fromDelayed_boxed_3499_,
        v_a_3492_,
        v_a_3493_,
        v_a_3494_,
        v_a_3495_,
        v_a_3496_,
        v_a_3497_,
    );
    crate::leanh::lean_dec(v_a_3497_);
    crate::leanh::lean_dec_ref(v_a_3496_);
    crate::leanh::lean_dec(v_a_3495_);
    crate::leanh::lean_dec_ref(v_a_3494_);
    crate::leanh::lean_dec(v_a_3493_);
    crate::leanh::lean_dec_ref(v_a_3492_);
    return v_res_3500_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(
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
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_Metavariable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ErrorUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
}
