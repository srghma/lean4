// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Metavariable
// Imports: Lean.PrettyPrinter.Delaborator.Basic Lean.Elab.ErrorUtils
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_replacePrefix, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4,
    l_Lean_Name_num___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node2,
    l_Lean_addMacroScope, l_Lean_reservedMacroScope, l_List_lengthTR___redArg,
    lean_erase_macro_scopes,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [109, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__0_value) as *mut LeanObject,9694982152043229093 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 117, 110, 105, 113, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__2_value) as *mut LeanObject,3978731030111751661 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 109, 118, 97, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__4_value) as *mut LeanObject,11782265356766657952 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value:
    LeanStringObject<14> = LeanStringObject {
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
        115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_0:
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
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__3_value
        ) as *mut LeanObject,
        11921244625177918938 as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5_value:
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
    m_data: [63, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6_value:
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
    m_data: [95, 0],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1_value:
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
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__0_value
        ) as *mut LeanObject,
        16016571949189376859 as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_getPPMVars___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_getPPMVarsAnonymous___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [32, 40, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 41, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [63, 95, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [10, 10, 65, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [32, 105, 110, 32, 116, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 39, 115, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 58, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [10, 10, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [86, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [86, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [32, 97, 98, 115, 101, 110, 116, 32, 102, 114, 111, 109, 32, 116, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 39, 115, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 58, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [32, 83, 117, 98, 115, 116, 105, 116, 117, 116, 105, 111, 110, 32, 105, 115, 32, 97, 119, 97, 105, 116, 105, 110, 103, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0_value: LeanStringObject<225> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 225, m_capacity: 225, m_length: 224, m_data: [83, 117, 98, 115, 116, 105, 116, 117, 116, 105, 111, 110, 32, 105, 115, 32, 100, 101, 108, 97, 121, 101, 100, 32, 117, 110, 116, 105, 108, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 39, 115, 32, 118, 97, 108, 117, 101, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 110, 111, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 44, 32, 115, 105, 110, 99, 101, 32, 97, 108, 108, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 32, 111, 102, 32, 116, 104, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 102, 114, 111, 109, 32, 105, 116, 115, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 119, 105, 108, 108, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 118, 97, 108, 105, 100, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 99, 111, 110, 116, 101, 120, 116, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value: LeanStringObject<89> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [80, 97, 114, 116, 32, 111, 102, 32, 116, 104, 101, 32, 101, 110, 99, 111, 100, 105, 110, 103, 32, 111, 102, 32, 116, 104, 101, 32, 42, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 42, 32, 109, 101, 99, 104, 97, 110, 105, 115, 109, 46, 32, 82, 101, 112, 114, 101, 115, 101, 110, 116, 115, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [44, 32, 119, 104, 105, 99, 104, 32, 104, 97, 115, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value: LeanStringObject<125> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 125, m_capacity: 125, m_length: 124, m_data: [91, 69, 114, 114, 111, 114, 58, 32, 84, 104, 105, 115, 32, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 32, 114, 101, 102, 101, 114, 115, 32, 116, 111, 32, 97, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 111, 110, 116, 101, 120, 116, 46, 32, 80, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 116, 104, 105, 115, 32, 105, 115, 115, 117, 101, 46, 93, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 97, 115, 115, 105, 103, 110, 101, 100, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value: LeanStringObject<88> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 88, m_capacity: 88, m_length: 87, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 97, 115, 115, 105, 103, 110, 101, 100, 44, 32, 98, 117, 116, 32, 105, 116, 32, 97, 112, 112, 101, 97, 114, 115, 32, 104, 101, 114, 101, 32, 118, 105, 97, 32, 97, 32, 42, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 42, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value: LeanStringObject<86> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 97, 115, 115, 105, 103, 110, 101, 100, 32, 100, 117, 101, 32, 116, 111, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 111, 110, 116, 101, 120, 116, 32, 100, 101, 112, 116, 104, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 97, 112, 112, 101, 97, 114, 115, 32, 104, 101, 114, 101, 32, 118, 105, 97, 32, 97, 32, 42, 100, 101, 108, 97, 121, 101, 100, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 42, 46, 32, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [10, 10, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 104, 97, 115, 32, 97, 32, 110, 97, 109, 101, 32, 98, 117, 116, 32, 105, 116, 32, 105, 115, 32, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9_value: LeanStringObject<221> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 221, m_capacity: 221, m_length: 220, m_data: [65, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 105, 110, 103, 32, 97, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 116, 104, 97, 116, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 115, 111, 108, 118, 101, 100, 32, 102, 111, 114, 32, 98, 121, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 100, 117, 114, 105, 110, 103, 32, 116, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 115, 115, 46, 32, 84, 104, 101, 121, 32, 97, 114, 101, 32, 99, 114, 101, 97, 116, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 97, 115, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 115, 32, 102, 111, 114, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 97, 110, 100, 32, 98, 121, 32, 96, 95, 96, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 32, 115, 121, 110, 116, 97, 120, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10_value: LeanStringObject<240> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 240, m_capacity: 240, m_length: 239, m_data: [65, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 105, 110, 103, 32, 97, 32, 116, 121, 112, 101, 99, 108, 97, 115, 115, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 119, 104, 111, 115, 101, 32, 115, 121, 110, 116, 104, 101, 115, 105, 115, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 112, 101, 110, 100, 105, 110, 103, 46, 32, 84, 104, 101, 121, 32, 99, 97, 110, 32, 98, 101, 32, 115, 111, 108, 118, 101, 100, 32, 102, 111, 114, 32, 98, 121, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 100, 117, 114, 105, 110, 103, 32, 116, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 115, 115, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 105, 110, 102, 101, 114, 114, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 97, 110, 100, 32, 116, 104, 101, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 109, 117, 115, 116, 32, 98, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11_value: LeanStringObject<235> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 235, m_capacity: 235, m_length: 234, m_data: [65, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 105, 110, 103, 32, 97, 32, 116, 97, 99, 116, 105, 99, 32, 103, 111, 97, 108, 32, 111, 114, 32, 97, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 119, 104, 111, 115, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 112, 101, 110, 100, 105, 110, 103, 46, 32, 84, 104, 101, 121, 32, 117, 115, 117, 97, 108, 108, 121, 32, 97, 99, 116, 32, 108, 105, 107, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 117, 110, 116, 105, 108, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 99, 111, 109, 112, 108, 101, 116, 101, 108, 121, 32, 115, 111, 108, 118, 101, 100, 32, 102, 111, 114, 46, 32, 84, 104, 101, 121, 32, 99, 97, 110, 32, 98, 101, 32, 99, 114, 101, 97, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 96, 63, 95, 96, 32, 97, 110, 100, 32, 96, 63, 110, 96, 32, 115, 121, 110, 116, 104, 101, 116, 105, 99, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 32, 115, 121, 110, 116, 97, 120, 46, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12_value: LeanStringObject<97> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [91, 69, 114, 114, 111, 114, 58, 32, 84, 104, 105, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 99, 111, 110, 116, 101, 120, 116, 46, 32, 80, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 116, 104, 105, 115, 32, 105, 115, 115, 117, 101, 46, 93, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12_value) as *mut LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(
    mut v_x_1751_: *mut LeanObject,
    mut v_x_1752_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1751_) == 0 {
        if lean_obj_tag(v_x_1752_) == 0 {
            let mut v___x_1753_: u8 = 0;
            v___x_1753_ = 1;
            return v___x_1753_;
        } else {
            let mut v___x_1754_: u8 = 0;
            v___x_1754_ = 0;
            return v___x_1754_;
        }
    } else {
        if lean_obj_tag(v_x_1752_) == 0 {
            let mut v___x_1755_: u8 = 0;
            v___x_1755_ = 0;
            return v___x_1755_;
        } else {
            let mut v_val_1756_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1757_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1758_: u8 = 0;
            v_val_1756_ = lean_ctor_get(v_x_1751_, 0);
            v_val_1757_ = lean_ctor_get(v_x_1752_, 0);
            v___x_1758_ = l_Lean_instBEqMVarId_beq(v_val_1756_, v_val_1757_);
            return v___x_1758_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0___boxed(
    mut v_x_1759_: *mut LeanObject,
    mut v_x_1760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1761_: u8 = 0;
    let mut v_r_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1761_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v_x_1759_, v_x_1760_);
    lean_dec(v_x_1760_);
    lean_dec(v_x_1759_);
    v_r_1762_ = lean_box((v_res_1761_) as usize);
    return v_r_1762_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(
    mut v_m_1772_: *mut LeanObject,
    mut v_mkMVarPlaceholder_1773_: *mut LeanObject,
    mut v_mkMVar_1774_: *mut LeanObject,
    mut v_mkMVarDead_1775_: *mut LeanObject,
    mut v_ppMVars_1776_: u8,
    mut v_ppMVarsAnonymous_1777_: u8,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
    mut v_a_1780_: *mut LeanObject,
    mut v_a_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v_userName_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1807_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_ppMVars_1776_ == 0 {
                    lean_dec_ref(v_mkMVarDead_1775_);
                    lean_dec_ref(v_mkMVar_1774_);
                    lean_dec(v_m_1772_);
                    lean_inc(v_a_1781_);
                    lean_inc_ref(v_a_1780_);
                    lean_inc(v_a_1779_);
                    lean_inc_ref(v_a_1778_);
                    v___x_1783_ = lean_apply_5(
                        v_mkMVarPlaceholder_1773_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                        lean_box(0),
                    );
                    return v___x_1783_;
                } else {
                    v___x_1784_ = l_Lean_MVarId_findDecl_x3f___redArg(v_m_1772_, v_a_1779_);
                    if lean_obj_tag(v___x_1784_) == 0 {
                        v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
                        lean_inc(v_a_1785_);
                        lean_dec_ref_known(v___x_1784_, 1);
                        if lean_obj_tag(v_a_1785_) == 1 {
                            v_val_1786_ = lean_ctor_get(v_a_1785_, 0);
                            v_isSharedCheck_1807_ = (!lean_is_exclusive(v_a_1785_)) as u8;
                            if v_isSharedCheck_1807_ == 0 {
                                v___x_1788_ = v_a_1785_;
                                v_isShared_1789_ = v_isSharedCheck_1807_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_val_1786_);
                                lean_dec(v_a_1785_);
                                v___x_1788_ = lean_box(0);
                                v_isShared_1789_ = v_isSharedCheck_1807_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1785_);
                            lean_dec_ref(v_mkMVarDead_1775_);
                            lean_dec_ref(v_mkMVarPlaceholder_1773_);
                            v___x_1808_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__3;
                            v___x_1809_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__5;
                            v___x_1810_ =
                                l_Lean_Name_replacePrefix(v_m_1772_, v___x_1808_, v___x_1809_);
                            lean_inc(v_a_1781_);
                            lean_inc_ref(v_a_1780_);
                            lean_inc(v_a_1779_);
                            lean_inc_ref(v_a_1778_);
                            v___x_1811_ = lean_apply_6(
                                v_mkMVar_1774_,
                                v___x_1810_,
                                v_a_1778_,
                                v_a_1779_,
                                v_a_1780_,
                                v_a_1781_,
                                lean_box(0),
                            );
                            return v___x_1811_;
                        }
                    } else {
                        lean_dec_ref(v_mkMVarDead_1775_);
                        lean_dec_ref(v_mkMVar_1774_);
                        lean_dec_ref(v_mkMVarPlaceholder_1773_);
                        lean_dec(v_m_1772_);
                        v_a_1812_ = lean_ctor_get(v___x_1784_, 0);
                        v_isSharedCheck_1819_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1819_ == 0 {
                            v___x_1814_ = v___x_1784_;
                            v_isShared_1815_ = v_isSharedCheck_1819_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1812_);
                            lean_dec(v___x_1784_);
                            v___x_1814_ = lean_box(0);
                            v_isShared_1815_ = v_isSharedCheck_1819_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_userName_1790_ = lean_ctor_get(v_val_1786_, 0);
                if lean_obj_tag(v_userName_1790_) == 0 {
                    lean_del_object(v___x_1788_);
                    lean_dec_ref(v_mkMVarDead_1775_);
                    lean_dec(v_m_1772_);
                    if v_ppMVarsAnonymous_1777_ == 0 {
                        lean_dec(v_val_1786_);
                        lean_dec_ref(v_mkMVar_1774_);
                        lean_inc(v_a_1781_);
                        lean_inc_ref(v_a_1780_);
                        lean_inc(v_a_1779_);
                        lean_inc_ref(v_a_1778_);
                        v___x_1791_ = lean_apply_5(
                            v_mkMVarPlaceholder_1773_,
                            v_a_1778_,
                            v_a_1779_,
                            v_a_1780_,
                            v_a_1781_,
                            lean_box(0),
                        );
                        return v___x_1791_;
                    } else {
                        lean_dec_ref(v_mkMVarPlaceholder_1773_);
                        v_index_1792_ = lean_ctor_get(v_val_1786_, 6);
                        lean_inc(v_index_1792_);
                        lean_dec(v_val_1786_);
                        v___x_1793_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg___closed__1;
                        v___x_1794_ = lean_unsigned_to_nat(1);
                        v___x_1795_ = lean_nat_add(v_index_1792_, v___x_1794_);
                        lean_dec(v_index_1792_);
                        v___x_1796_ = l_Lean_Name_num___override(v___x_1793_, v___x_1795_);
                        lean_inc(v_a_1781_);
                        lean_inc_ref(v_a_1780_);
                        lean_inc(v_a_1779_);
                        lean_inc_ref(v_a_1778_);
                        v___x_1797_ = lean_apply_6(
                            v_mkMVar_1774_,
                            v___x_1796_,
                            v_a_1778_,
                            v_a_1779_,
                            v_a_1780_,
                            v_a_1781_,
                            lean_box(0),
                        );
                        return v___x_1797_;
                    }
                } else {
                    lean_inc(v_userName_1790_);
                    lean_dec(v_val_1786_);
                    lean_dec_ref(v_mkMVarPlaceholder_1773_);
                    v___x_1798_ = lean_st_ref_get(v_a_1779_);
                    v_mctx_1799_ = lean_ctor_get(v___x_1798_, 0);
                    lean_inc_ref(v_mctx_1799_);
                    lean_dec(v___x_1798_);
                    if v_isShared_1789_ == 0 {
                        lean_ctor_set(v___x_1788_, 0, v_m_1772_);
                        v___x_1801_ = v___x_1788_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_m_1772_);
                        v___x_1801_ = v_reuseFailAlloc_1806_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1802_ =
                    l_Lean_MetavarContext_findUserName_x3f(v_mctx_1799_, v_userName_1790_);
                lean_dec_ref(v_mctx_1799_);
                v___x_1803_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_1801_, v___x_1802_);
                lean_dec(v___x_1802_);
                lean_dec_ref(v___x_1801_);
                if v___x_1803_ == 0 {
                    lean_dec_ref(v_mkMVar_1774_);
                    lean_inc(v_a_1781_);
                    lean_inc_ref(v_a_1780_);
                    lean_inc(v_a_1779_);
                    lean_inc_ref(v_a_1778_);
                    v___x_1804_ = lean_apply_6(
                        v_mkMVarDead_1775_,
                        v_userName_1790_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                        lean_box(0),
                    );
                    return v___x_1804_;
                } else {
                    lean_dec_ref(v_mkMVarDead_1775_);
                    lean_inc(v_a_1781_);
                    lean_inc_ref(v_a_1780_);
                    lean_inc(v_a_1779_);
                    lean_inc_ref(v_a_1778_);
                    v___x_1805_ = lean_apply_6(
                        v_mkMVar_1774_,
                        v_userName_1790_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                        lean_box(0),
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
                    v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
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
    mut v_m_1820_: *mut LeanObject,
    mut v_mkMVarPlaceholder_1821_: *mut LeanObject,
    mut v_mkMVar_1822_: *mut LeanObject,
    mut v_mkMVarDead_1823_: *mut LeanObject,
    mut v_ppMVars_1824_: *mut LeanObject,
    mut v_ppMVarsAnonymous_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
    mut v_a_1828_: *mut LeanObject,
    mut v_a_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ppMVars_boxed_1831_: u8 = 0;
    let mut v_ppMVarsAnonymous_boxed_1832_: u8 = 0;
    let mut v_res_1833_: *mut LeanObject = core::ptr::null_mut();
    v_ppMVars_boxed_1831_ = (lean_unbox(v_ppMVars_1824_) as u8);
    v_ppMVarsAnonymous_boxed_1832_ = (lean_unbox(v_ppMVarsAnonymous_1825_) as u8);
    v_res_1833_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_1820_, v_mkMVarPlaceholder_1821_, v_mkMVar_1822_, v_mkMVarDead_1823_, v_ppMVars_boxed_1831_, v_ppMVarsAnonymous_boxed_1832_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
    lean_dec(v_a_1829_);
    lean_dec_ref(v_a_1828_);
    lean_dec(v_a_1827_);
    lean_dec_ref(v_a_1826_);
    return v_res_1833_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux(
    mut v_00_u03b1_1834_: *mut LeanObject,
    mut v_m_1835_: *mut LeanObject,
    mut v_mkMVarPlaceholder_1836_: *mut LeanObject,
    mut v_mkMVar_1837_: *mut LeanObject,
    mut v_mkMVarDead_1838_: *mut LeanObject,
    mut v_ppMVars_1839_: u8,
    mut v_ppMVarsAnonymous_1840_: u8,
    mut v_a_1841_: *mut LeanObject,
    mut v_a_1842_: *mut LeanObject,
    mut v_a_1843_: *mut LeanObject,
    mut v_a_1844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    v___x_1846_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_1835_, v_mkMVarPlaceholder_1836_, v_mkMVar_1837_, v_mkMVarDead_1838_, v_ppMVars_1839_, v_ppMVarsAnonymous_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
    return v___x_1846_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___boxed(
    mut v_00_u03b1_1847_: *mut LeanObject,
    mut v_m_1848_: *mut LeanObject,
    mut v_mkMVarPlaceholder_1849_: *mut LeanObject,
    mut v_mkMVar_1850_: *mut LeanObject,
    mut v_mkMVarDead_1851_: *mut LeanObject,
    mut v_ppMVars_1852_: *mut LeanObject,
    mut v_ppMVarsAnonymous_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
    mut v_a_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ppMVars_boxed_1859_: u8 = 0;
    let mut v_ppMVarsAnonymous_boxed_1860_: u8 = 0;
    let mut v_res_1861_: *mut LeanObject = core::ptr::null_mut();
    v_ppMVars_boxed_1859_ = (lean_unbox(v_ppMVars_1852_) as u8);
    v_ppMVarsAnonymous_boxed_1860_ = (lean_unbox(v_ppMVarsAnonymous_1853_) as u8);
    v_res_1861_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux(v_00_u03b1_1847_, v_m_1848_, v_mkMVarPlaceholder_1849_, v_mkMVar_1850_, v_mkMVarDead_1851_, v_ppMVars_boxed_1859_, v_ppMVarsAnonymous_boxed_1860_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
    lean_dec(v_a_1857_);
    lean_dec_ref(v_a_1856_);
    lean_dec(v_a_1855_);
    lean_dec_ref(v_a_1854_);
    return v_res_1861_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0(
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1867_ = lean_ctor_get(v___y_1864_, 5);
    v___x_1868_ = 0;
    v___x_1869_ = l_Lean_SourceInfo_fromRef(v_ref_1867_, v___x_1868_);
    v___x_1870_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1870_, 0, v___x_1869_);
    return v___x_1870_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0___boxed(
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1876_: *mut LeanObject = core::ptr::null_mut();
    v_res_1876_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__0(
        v___y_1871_,
        v___y_1872_,
        v___y_1873_,
        v___y_1874_,
    );
    lean_dec(v___y_1874_);
    lean_dec_ref(v___y_1873_);
    lean_dec(v___y_1872_);
    lean_dec_ref(v___y_1871_);
    return v_res_1876_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1(
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1893_ = lean_ctor_get(v___y_1890_, 5);
    v___x_1894_ = 0;
    v___x_1895_ = l_Lean_SourceInfo_fromRef(v_ref_1893_, v___x_1894_);
    v___x_1896_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4;
    v___x_1897_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
    lean_inc_n(v___x_1895_, 2);
    v___x_1898_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1898_, 0, v___x_1895_);
    lean_ctor_set(v___x_1898_, 1, v___x_1897_);
    v___x_1899_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__6;
    v___x_1900_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1900_, 0, v___x_1895_);
    lean_ctor_set(v___x_1900_, 1, v___x_1899_);
    v___x_1901_ = l_Lean_Syntax_node2(v___x_1895_, v___x_1896_, v___x_1898_, v___x_1900_);
    v___x_1902_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1902_, 0, v___x_1901_);
    return v___x_1902_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___boxed(
    mut v___y_1903_: *mut LeanObject,
    mut v___y_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1908_: *mut LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1(
        v___y_1903_,
        v___y_1904_,
        v___y_1905_,
        v___y_1906_,
    );
    lean_dec(v___y_1906_);
    lean_dec_ref(v___y_1905_);
    lean_dec(v___y_1904_);
    lean_dec_ref(v___y_1903_);
    return v_res_1908_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2(
    mut v___f_1909_: *mut LeanObject,
    mut v_n_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut v_a_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1914_);
                lean_inc_ref(v___y_1913_);
                lean_inc(v___y_1912_);
                lean_inc_ref(v___y_1911_);
                v___x_1916_ = lean_apply_5(
                    v___f_1909_,
                    v___y_1911_,
                    v___y_1912_,
                    v___y_1913_,
                    v___y_1914_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1916_) == 0 {
                    v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
                    v_isSharedCheck_1929_ = (!lean_is_exclusive(v___x_1916_)) as u8;
                    if v_isSharedCheck_1929_ == 0 {
                        v___x_1919_ = v___x_1916_;
                        v_isShared_1920_ = v_isSharedCheck_1929_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1917_);
                        lean_dec(v___x_1916_);
                        v___x_1919_ = lean_box(0);
                        v_isShared_1920_ = v_isSharedCheck_1929_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_n_1910_);
                    v_a_1930_ = lean_ctor_get(v___x_1916_, 0);
                    v_isSharedCheck_1937_ = (!lean_is_exclusive(v___x_1916_)) as u8;
                    if v_isSharedCheck_1937_ == 0 {
                        v___x_1932_ = v___x_1916_;
                        v_isShared_1933_ = v_isSharedCheck_1937_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1930_);
                        lean_dec(v___x_1916_);
                        v___x_1932_ = lean_box(0);
                        v_isShared_1933_ = v_isSharedCheck_1937_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1921_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__4;
                v___x_1922_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
                lean_inc(v_a_1917_);
                v___x_1923_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1923_, 0, v_a_1917_);
                lean_ctor_set(v___x_1923_, 1, v___x_1922_);
                v___x_1924_ = lean_mk_syntax_ident(v_n_1910_);
                v___x_1925_ = l_Lean_Syntax_node2(v_a_1917_, v___x_1921_, v___x_1923_, v___x_1924_);
                if v_isShared_1920_ == 0 {
                    lean_ctor_set(v___x_1919_, 0, v___x_1925_);
                    v___x_1927_ = v___x_1919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
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
                    v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
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
    mut v___f_1938_: *mut LeanObject,
    mut v_n_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1945_: *mut LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__2(
        v___f_1938_,
        v_n_1939_,
        v___y_1940_,
        v___y_1941_,
        v___y_1942_,
        v___y_1943_,
    );
    lean_dec(v___y_1943_);
    lean_dec_ref(v___y_1942_);
    lean_dec(v___y_1941_);
    lean_dec_ref(v___y_1940_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(
    mut v___f_1949_: *mut LeanObject,
    mut v_m_1950_: *mut LeanObject,
    mut v_n_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1961_: u8 = 0;
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v_a_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1955_);
                lean_inc_ref(v___y_1954_);
                lean_inc(v___y_1953_);
                lean_inc_ref(v___y_1952_);
                v___x_1957_ = lean_apply_5(
                    v___f_1949_,
                    v___y_1952_,
                    v___y_1953_,
                    v___y_1954_,
                    v___y_1955_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1957_) == 0 {
                    v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
                    v_isSharedCheck_1974_ = (!lean_is_exclusive(v___x_1957_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v___x_1960_ = v___x_1957_;
                        v_isShared_1961_ = v_isSharedCheck_1974_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1958_);
                        lean_dec(v___x_1957_);
                        v___x_1960_ = lean_box(0);
                        v_isShared_1961_ = v_isSharedCheck_1974_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_n_1951_);
                    lean_dec(v_m_1950_);
                    v_a_1975_ = lean_ctor_get(v___x_1957_, 0);
                    v_isSharedCheck_1982_ = (!lean_is_exclusive(v___x_1957_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1977_ = v___x_1957_;
                        v_isShared_1978_ = v_isSharedCheck_1982_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1975_);
                        lean_dec(v___x_1957_);
                        v___x_1977_ = lean_box(0);
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
                lean_inc(v_a_1958_);
                v___x_1968_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1968_, 0, v_a_1958_);
                lean_ctor_set(v___x_1968_, 1, v___x_1967_);
                v___x_1969_ = lean_mk_syntax_ident(v___x_1965_);
                v___x_1970_ = l_Lean_Syntax_node2(v_a_1958_, v___x_1966_, v___x_1968_, v___x_1969_);
                if v_isShared_1961_ == 0 {
                    lean_ctor_set(v___x_1960_, 0, v___x_1970_);
                    v___x_1972_ = v___x_1960_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
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
                    v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
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
    mut v___f_1983_: *mut LeanObject,
    mut v_m_1984_: *mut LeanObject,
    mut v_n_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
    mut v___y_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1991_: *mut LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3(
        v___f_1983_,
        v_m_1984_,
        v_n_1985_,
        v___y_1986_,
        v___y_1987_,
        v___y_1988_,
        v___y_1989_,
    );
    lean_dec(v___y_1989_);
    lean_dec_ref(v___y_1988_);
    lean_dec(v___y_1987_);
    lean_dec_ref(v___y_1986_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_delabMVarAux(
    mut v_m_1998_: *mut LeanObject,
    mut v_a_1999_: *mut LeanObject,
    mut v_a_2000_: *mut LeanObject,
    mut v_a_2001_: *mut LeanObject,
    mut v_a_2002_: *mut LeanObject,
    mut v_a_2003_: *mut LeanObject,
    mut v_a_2004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut v_a_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2007_) == 0 {
                    v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
                    lean_inc(v_a_2008_);
                    lean_dec_ref_known(v___x_2007_, 1);
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
                    if lean_obj_tag(v___x_2010_) == 0 {
                        v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
                        lean_inc(v_a_2011_);
                        lean_dec_ref_known(v___x_2010_, 1);
                        v___f_2012_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__2;
                        v___f_2013_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__3;
                        v___f_2014_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___closed__4;
                        lean_inc(v_m_1998_);
                        v___f_2015_ = lean_alloc_closure(
                            l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__3___boxed
                                as *mut core::ffi::c_void,
                            8,
                            2,
                        );
                        lean_closure_set(v___f_2015_, 0, v___f_2012_);
                        lean_closure_set(v___f_2015_, 1, v_m_1998_);
                        v___x_2016_ = (lean_unbox(v_a_2008_) as u8);
                        lean_dec(v_a_2008_);
                        v___x_2017_ = (lean_unbox(v_a_2011_) as u8);
                        lean_dec(v_a_2011_);
                        v___x_2018_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_1998_, v___f_2013_, v___f_2014_, v___f_2015_, v___x_2016_, v___x_2017_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
                        return v___x_2018_;
                    } else {
                        lean_dec(v_a_2008_);
                        lean_dec(v_m_1998_);
                        v_a_2019_ = lean_ctor_get(v___x_2010_, 0);
                        v_isSharedCheck_2026_ = (!lean_is_exclusive(v___x_2010_)) as u8;
                        if v_isSharedCheck_2026_ == 0 {
                            v___x_2021_ = v___x_2010_;
                            v_isShared_2022_ = v_isSharedCheck_2026_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2019_);
                            lean_dec(v___x_2010_);
                            v___x_2021_ = lean_box(0);
                            v_isShared_2022_ = v_isSharedCheck_2026_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_m_1998_);
                    v_a_2027_ = lean_ctor_get(v___x_2007_, 0);
                    v_isSharedCheck_2034_ = (!lean_is_exclusive(v___x_2007_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2029_ = v___x_2007_;
                        v_isShared_2030_ = v_isSharedCheck_2034_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2027_);
                        lean_dec(v___x_2007_);
                        v___x_2029_ = lean_box(0);
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
                    v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
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
                    v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
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
    mut v_m_2035_: *mut LeanObject,
    mut v_a_2036_: *mut LeanObject,
    mut v_a_2037_: *mut LeanObject,
    mut v_a_2038_: *mut LeanObject,
    mut v_a_2039_: *mut LeanObject,
    mut v_a_2040_: *mut LeanObject,
    mut v_a_2041_: *mut LeanObject,
    mut v_a_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2043_: *mut LeanObject = core::ptr::null_mut();
    v_res_2043_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux(
        v_m_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_,
    );
    lean_dec(v_a_2041_);
    lean_dec_ref(v_a_2040_);
    lean_dec(v_a_2039_);
    lean_dec_ref(v_a_2038_);
    lean_dec(v_a_2037_);
    lean_dec_ref(v_a_2036_);
    return v_res_2043_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0(
    mut v_n_2045_: *mut LeanObject,
    mut v___y_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    v___x_2051_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
    v___x_2052_ = 1;
    v___x_2053_ = l_Lean_Name_toString(v_n_2045_, v___x_2052_);
    v___x_2054_ = lean_string_append(v___x_2051_, v___x_2053_);
    lean_dec_ref(v___x_2053_);
    v___x_2055_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0;
    v___x_2056_ = lean_string_append(v___x_2054_, v___x_2055_);
    v___x_2057_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2057_, 0, v___x_2056_);
    return v___x_2057_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___boxed(
    mut v_n_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2064_: *mut LeanObject = core::ptr::null_mut();
    v_res_2064_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0(v_n_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
    lean_dec(v___y_2062_);
    lean_dec_ref(v___y_2061_);
    lean_dec(v___y_2060_);
    lean_dec_ref(v___y_2059_);
    return v_res_2064_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1(
    mut v_n_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Lean_PrettyPrinter_Delaborator_delabMVarAux___lam__1___closed__5;
    v___x_2072_ = 1;
    v___x_2073_ = l_Lean_Name_toString(v_n_2065_, v___x_2072_);
    v___x_2074_ = lean_string_append(v___x_2071_, v___x_2073_);
    lean_dec_ref(v___x_2073_);
    v___x_2075_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2075_, 0, v___x_2074_);
    return v___x_2075_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1___boxed(
    mut v_n_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2082_: *mut LeanObject = core::ptr::null_mut();
    v_res_2082_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__1(v_n_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
    lean_dec(v___y_2080_);
    lean_dec_ref(v___y_2079_);
    lean_dec(v___y_2078_);
    lean_dec_ref(v___y_2077_);
    return v_res_2082_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2(
    mut v___x_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
    mut v___y_2086_: *mut LeanObject,
    mut v___y_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2089_, 0, v___x_2083_);
    return v___x_2089_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2___boxed(
    mut v___x_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2096_: *mut LeanObject = core::ptr::null_mut();
    v_res_2096_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__2(v___x_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
    lean_dec(v___y_2094_);
    lean_dec_ref(v___y_2093_);
    lean_dec(v___y_2092_);
    lean_dec_ref(v___y_2091_);
    return v_res_2096_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(
    mut v_m_2102_: *mut LeanObject,
    mut v_a_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
    mut v_a_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    v_options_2108_ = lean_ctor_get(v_a_2105_, 2);
    v___f_2109_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__0;
    v___f_2110_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__1;
    v___f_2111_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___closed__3;
    v___x_2112_ = l_Lean_getPPMVars(v_options_2108_);
    v___x_2113_ = l_Lean_getPPMVarsAnonymous(v_options_2108_);
    v___x_2114_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux___redArg(v_m_2102_, v___f_2111_, v___f_2110_, v___f_2109_, v___x_2112_, v___x_2113_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
    return v___x_2114_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___boxed(
    mut v_m_2115_: *mut LeanObject,
    mut v_a_2116_: *mut LeanObject,
    mut v_a_2117_: *mut LeanObject,
    mut v_a_2118_: *mut LeanObject,
    mut v_a_2119_: *mut LeanObject,
    mut v_a_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2121_: *mut LeanObject = core::ptr::null_mut();
    v_res_2121_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_m_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
    lean_dec(v_a_2119_);
    lean_dec_ref(v_a_2118_);
    lean_dec(v_a_2117_);
    lean_dec_ref(v_a_2116_);
    return v_res_2121_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(
    mut v_a_2122_: *mut LeanObject,
    mut v_x_2123_: *mut LeanObject,
) -> u8 {
    let mut v___x_2124_: u8 = 0;
    let mut v_key_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2123_) == 0 {
                    v___x_2124_ = 0;
                    return v___x_2124_;
                } else {
                    v_key_2125_ = lean_ctor_get(v_x_2123_, 0);
                    v_tail_2126_ = lean_ctor_get(v_x_2123_, 2);
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
    mut v_a_2129_: *mut LeanObject,
    mut v_x_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2131_: u8 = 0;
    let mut v_r_2132_: *mut LeanObject = core::ptr::null_mut();
    v_res_2131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_2129_, v_x_2130_);
    lean_dec(v_x_2130_);
    lean_dec(v_a_2129_);
    v_r_2132_ = lean_box((v_res_2131_) as usize);
    return v_r_2132_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(
    mut v_m_2133_: *mut LeanObject,
    mut v_a_2134_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    v_buckets_2135_ = lean_ctor_get(v_m_2133_, 1);
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
    mut v_m_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2153_: u8 = 0;
    let mut v_r_2154_: *mut LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_2151_, v_a_2152_);
    lean_dec(v_a_2152_);
    lean_dec_ref(v_m_2151_);
    v_r_2154_ = lean_box((v_res_2153_) as usize);
    return v_r_2154_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_x_2155_: *mut LeanObject,
    mut v_x_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2156_) == 0 {
                    return v_x_2155_;
                } else {
                    v_key_2157_ = lean_ctor_get(v_x_2156_, 0);
                    v_value_2158_ = lean_ctor_get(v_x_2156_, 1);
                    v_tail_2159_ = lean_ctor_get(v_x_2156_, 2);
                    v_isSharedCheck_2182_ = (!lean_is_exclusive(v_x_2156_)) as u8;
                    if v_isSharedCheck_2182_ == 0 {
                        v___x_2161_ = v_x_2156_;
                        v_isShared_2162_ = v_isSharedCheck_2182_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2159_);
                        lean_inc(v_value_2158_);
                        lean_inc(v_key_2157_);
                        lean_dec(v_x_2156_);
                        v___x_2161_ = lean_box(0);
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
                lean_inc(v___x_2176_);
                if v_isShared_2162_ == 0 {
                    lean_ctor_set(v___x_2161_, 2, v___x_2176_);
                    v___x_2178_ = v___x_2161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_key_2157_);
                    lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_value_2158_);
                    lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2176_);
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
    mut v_i_2183_: *mut LeanObject,
    mut v_source_2184_: *mut LeanObject,
    mut v_target_2185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v_es_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2186_ = lean_array_get_size(v_source_2184_);
                v___x_2187_ = lean_nat_dec_lt(v_i_2183_, v___x_2186_);
                if v___x_2187_ == 0 {
                    lean_dec_ref(v_source_2184_);
                    lean_dec(v_i_2183_);
                    return v_target_2185_;
                } else {
                    v_es_2188_ = lean_array_fget(v_source_2184_, v_i_2183_);
                    v___x_2189_ = lean_box(0);
                    v_source_2190_ = lean_array_fset(v_source_2184_, v_i_2183_, v___x_2189_);
                    v_target_2191_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_target_2185_, v_es_2188_);
                    v___x_2192_ = lean_unsigned_to_nat(1);
                    v___x_2193_ = lean_nat_add(v_i_2183_, v___x_2192_);
                    lean_dec(v_i_2183_);
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
    mut v_data_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    v___x_2196_ = lean_array_get_size(v_data_2195_);
    v___x_2197_ = lean_unsigned_to_nat(2);
    v_nbuckets_2198_ = lean_nat_mul(v___x_2196_, v___x_2197_);
    v___x_2199_ = lean_unsigned_to_nat(0);
    v___x_2200_ = lean_box(0);
    v___x_2201_ = lean_mk_array(v_nbuckets_2198_, v___x_2200_);
    v___x_2202_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v___x_2199_, v_data_2195_, v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(
    mut v_m_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
    mut v_b_2205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v_val_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut v_unused_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2206_ = lean_ctor_get(v_m_2203_, 0);
                v_buckets_2207_ = lean_ctor_get(v_m_2203_, 1);
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
                    lean_inc_ref(v_buckets_2207_);
                    lean_inc(v_size_2206_);
                    v_isSharedCheck_2243_ = (!lean_is_exclusive(v_m_2203_)) as u8;
                    if v_isSharedCheck_2243_ == 0 {
                        v_unused_2244_ = lean_ctor_get(v_m_2203_, 1);
                        lean_dec(v_unused_2244_);
                        v_unused_2245_ = lean_ctor_get(v_m_2203_, 0);
                        lean_dec(v_unused_2245_);
                        v___x_2224_ = v_m_2203_;
                        v_isShared_2225_ = v_isSharedCheck_2243_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2203_);
                        v___x_2224_ = lean_box(0);
                        v_isShared_2225_ = v_isSharedCheck_2243_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2205_);
                    lean_dec(v_a_2204_);
                    return v_m_2203_;
                }
            }
            1 => {
                v___x_2226_ = lean_unsigned_to_nat(1);
                v_size_x27_2227_ = lean_nat_add(v_size_2206_, v___x_2226_);
                lean_dec(v_size_2206_);
                lean_inc(v_bkt_2221_);
                v___x_2228_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2228_, 0, v_a_2204_);
                lean_ctor_set(v___x_2228_, 1, v_b_2205_);
                lean_ctor_set(v___x_2228_, 2, v_bkt_2221_);
                v_buckets_x27_2229_ = lean_array_uset(v_buckets_2207_, v___x_2220_, v___x_2228_);
                v___x_2230_ = lean_unsigned_to_nat(4);
                v___x_2231_ = lean_nat_mul(v_size_x27_2227_, v___x_2230_);
                v___x_2232_ = lean_unsigned_to_nat(3);
                v___x_2233_ = lean_nat_div(v___x_2231_, v___x_2232_);
                lean_dec(v___x_2231_);
                v___x_2234_ = lean_array_get_size(v_buckets_x27_2229_);
                v___x_2235_ = lean_nat_dec_le(v___x_2233_, v___x_2234_);
                lean_dec(v___x_2233_);
                if v___x_2235_ == 0 {
                    v_val_2236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_buckets_x27_2229_);
                    if v_isShared_2225_ == 0 {
                        lean_ctor_set(v___x_2224_, 1, v_val_2236_);
                        lean_ctor_set(v___x_2224_, 0, v_size_x27_2227_);
                        v___x_2238_ = v___x_2224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_size_x27_2227_);
                        lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_val_2236_);
                        v___x_2238_ = v_reuseFailAlloc_2239_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2225_ == 0 {
                        lean_ctor_set(v___x_2224_, 1, v_buckets_x27_2229_);
                        lean_ctor_set(v___x_2224_, 0, v_size_x27_2227_);
                        v___x_2241_ = v___x_2224_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_size_x27_2227_);
                        lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_buckets_x27_2229_);
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
    mut v_val_2249_: *mut LeanObject,
    mut v_as_2250_: *mut LeanObject,
    mut v_sz_2251_: usize,
    mut v_i_2252_: usize,
    mut v_b_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v_snd_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v_array_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v_lctx_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: u8 = 0;
    let mut v_fvarId_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2337_: u8 = 0;
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2347_: u8 = 0;
    let mut v_unused_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_unused_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2260_ = lean_usize_dec_lt(v_i_2252_, v_sz_2251_);
                if v___x_2260_ == 0 {
                    lean_dec_ref(v_val_2249_);
                    v___x_2261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2261_, 0, v_b_2253_);
                    return v___x_2261_;
                } else {
                    v_snd_2262_ = lean_ctor_get(v_b_2253_, 1);
                    v_isSharedCheck_2352_ = (!lean_is_exclusive(v_b_2253_)) as u8;
                    if v_isSharedCheck_2352_ == 0 {
                        v_unused_2353_ = lean_ctor_get(v_b_2253_, 0);
                        lean_dec(v_unused_2353_);
                        v___x_2264_ = v_b_2253_;
                        v_isShared_2265_ = v_isSharedCheck_2352_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_2262_);
                        lean_dec(v_b_2253_);
                        v___x_2264_ = lean_box(0);
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
                v_snd_2266_ = lean_ctor_get(v_snd_2262_, 1);
                v_fst_2267_ = lean_ctor_get(v_snd_2262_, 0);
                v_isSharedCheck_2351_ = (!lean_is_exclusive(v_snd_2262_)) as u8;
                if v_isSharedCheck_2351_ == 0 {
                    v___x_2269_ = v_snd_2262_;
                    v_isShared_2270_ = v_isSharedCheck_2351_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_2266_);
                    lean_inc(v_fst_2267_);
                    lean_dec(v_snd_2262_);
                    v___x_2269_ = lean_box(0);
                    v_isShared_2270_ = v_isSharedCheck_2351_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_2271_ = lean_ctor_get(v_snd_2266_, 0);
                v_start_2272_ = lean_ctor_get(v_snd_2266_, 1);
                v_stop_2273_ = lean_ctor_get(v_snd_2266_, 2);
                v___x_2274_ = lean_box(0);
                v___x_2275_ = lean_nat_dec_lt(v_start_2272_, v_stop_2273_);
                if v___x_2275_ == 0 {
                    lean_dec_ref(v_val_2249_);
                    if v_isShared_2270_ == 0 {
                        v___x_2277_ = v___x_2269_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_fst_2267_);
                        lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_snd_2266_);
                        v___x_2277_ = v_reuseFailAlloc_2282_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_2273_);
                    lean_inc(v_start_2272_);
                    lean_inc_ref(v_array_2271_);
                    v_isSharedCheck_2347_ = (!lean_is_exclusive(v_snd_2266_)) as u8;
                    if v_isSharedCheck_2347_ == 0 {
                        v_unused_2348_ = lean_ctor_get(v_snd_2266_, 2);
                        lean_dec(v_unused_2348_);
                        v_unused_2349_ = lean_ctor_get(v_snd_2266_, 1);
                        lean_dec(v_unused_2349_);
                        v_unused_2350_ = lean_ctor_get(v_snd_2266_, 0);
                        lean_dec(v_unused_2350_);
                        v___x_2284_ = v_snd_2266_;
                        v_isShared_2285_ = v_isSharedCheck_2347_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_snd_2266_);
                        v___x_2284_ = lean_box(0);
                        v_isShared_2285_ = v_isSharedCheck_2347_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2265_ == 0 {
                    lean_ctor_set(v___x_2264_, 1, v___x_2277_);
                    lean_ctor_set(v___x_2264_, 0, v___x_2274_);
                    v___x_2279_ = v___x_2264_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2274_);
                    lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2277_);
                    v___x_2279_ = v_reuseFailAlloc_2281_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2280_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2280_, 0, v___x_2279_);
                return v___x_2280_;
            }
            6 => {
                v_lctx_2286_ = lean_ctor_get(v_val_2249_, 1);
                v___x_2287_ = lean_array_fget(v_array_2271_, v_start_2272_);
                v_a_2288_ = lean_array_uget_borrowed(v_as_2250_, v_i_2252_);
                v___x_2289_ = lean_unsigned_to_nat(1);
                v___x_2290_ = lean_nat_add(v_start_2272_, v___x_2289_);
                lean_dec(v_start_2272_);
                if v_isShared_2285_ == 0 {
                    lean_ctor_set(v___x_2284_, 1, v___x_2290_);
                    v___x_2292_ = v___x_2284_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_array_2271_);
                    lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2290_);
                    lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_stop_2273_);
                    v___x_2292_ = v_reuseFailAlloc_2346_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2293_ = l_Lean_Expr_fvarId_x21(v_a_2288_);
                lean_inc_ref(v_lctx_2286_);
                v___x_2294_ = lean_local_ctx_find(v_lctx_2286_, v___x_2293_);
                if lean_obj_tag(v___x_2294_) == 1 {
                    v_val_2295_ = lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2337_ = (!lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2337_ == 0 {
                        v___x_2297_ = v___x_2294_;
                        v_isShared_2298_ = v_isSharedCheck_2337_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_2295_);
                        lean_dec(v___x_2294_);
                        v___x_2297_ = lean_box(0);
                        v_isShared_2298_ = v_isSharedCheck_2337_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2294_);
                    lean_dec(v___x_2287_);
                    lean_dec_ref(v_val_2249_);
                    v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0;
                    if v_isShared_2270_ == 0 {
                        lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                        v___x_2340_ = v___x_2269_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_fst_2267_);
                        lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2292_);
                        v___x_2340_ = v_reuseFailAlloc_2345_;
                        state = 19;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2299_ = 0;
                v___x_2300_ = l_Lean_LocalDecl_hasValue(v_val_2295_, v___x_2299_);
                lean_dec(v_val_2295_);
                if v___x_2300_ == 0 {
                    if lean_obj_tag(v___x_2287_) == 1 {
                        v_fvarId_2301_ = lean_ctor_get(v___x_2287_, 0);
                        lean_inc(v_fvarId_2301_);
                        lean_dec_ref_known(v___x_2287_, 1);
                        v___x_2302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_fst_2267_, v_fvarId_2301_);
                        if v___x_2302_ == 0 {
                            lean_del_object(v___x_2297_);
                            v___x_2303_ = lean_box(0);
                            v___x_2304_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_fst_2267_, v_fvarId_2301_, v___x_2303_);
                            if v_isShared_2270_ == 0 {
                                lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                                lean_ctor_set(v___x_2269_, 0, v___x_2304_);
                                v___x_2306_ = v___x_2269_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2304_);
                                lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2292_);
                                v___x_2306_ = v_reuseFailAlloc_2310_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec(v_fvarId_2301_);
                            lean_dec_ref(v_val_2249_);
                            v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0;
                            if v_isShared_2270_ == 0 {
                                lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                                v___x_2313_ = v___x_2269_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_fst_2267_);
                                lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2292_);
                                v___x_2313_ = v_reuseFailAlloc_2320_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2287_);
                        lean_dec_ref(v_val_2249_);
                        v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___closed__0;
                        if v_isShared_2270_ == 0 {
                            lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                            v___x_2323_ = v___x_2269_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2267_);
                            lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2292_);
                            v___x_2323_ = v_reuseFailAlloc_2330_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2297_);
                    lean_dec(v___x_2287_);
                    if v_isShared_2270_ == 0 {
                        lean_ctor_set(v___x_2269_, 1, v___x_2292_);
                        v___x_2332_ = v___x_2269_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_fst_2267_);
                        lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___x_2292_);
                        v___x_2332_ = v_reuseFailAlloc_2336_;
                        state = 17;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2265_ == 0 {
                    lean_ctor_set(v___x_2264_, 1, v___x_2306_);
                    lean_ctor_set(v___x_2264_, 0, v___x_2274_);
                    v___x_2308_ = v___x_2264_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2274_);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___x_2306_);
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
                    lean_ctor_set(v___x_2264_, 1, v___x_2313_);
                    lean_ctor_set(v___x_2264_, 0, v___x_2311_);
                    v___x_2315_ = v___x_2264_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2311_);
                    lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2313_);
                    v___x_2315_ = v_reuseFailAlloc_2319_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2298_ == 0 {
                    lean_ctor_set_tag(v___x_2297_, 0);
                    lean_ctor_set(v___x_2297_, 0, v___x_2315_);
                    v___x_2317_ = v___x_2297_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
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
                    lean_ctor_set(v___x_2264_, 1, v___x_2323_);
                    lean_ctor_set(v___x_2264_, 0, v___x_2321_);
                    v___x_2325_ = v___x_2264_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2321_);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2323_);
                    v___x_2325_ = v_reuseFailAlloc_2329_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2298_ == 0 {
                    lean_ctor_set_tag(v___x_2297_, 0);
                    lean_ctor_set(v___x_2297_, 0, v___x_2325_);
                    v___x_2327_ = v___x_2297_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
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
                    lean_ctor_set(v___x_2264_, 1, v___x_2332_);
                    lean_ctor_set(v___x_2264_, 0, v___x_2274_);
                    v___x_2334_ = v___x_2264_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2274_);
                    lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2332_);
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
                    lean_ctor_set(v___x_2264_, 1, v___x_2340_);
                    lean_ctor_set(v___x_2264_, 0, v___x_2338_);
                    v___x_2342_ = v___x_2264_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2338_);
                    lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2340_);
                    v___x_2342_ = v_reuseFailAlloc_2344_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2343_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2343_, 0, v___x_2342_);
                return v___x_2343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg___boxed(
    mut v_val_2354_: *mut LeanObject,
    mut v_as_2355_: *mut LeanObject,
    mut v_sz_2356_: *mut LeanObject,
    mut v_i_2357_: *mut LeanObject,
    mut v_b_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2360_: usize = 0;
    let mut v_i_boxed_2361_: usize = 0;
    let mut v_res_2362_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2360_ = lean_unbox_usize(v_sz_2356_);
    lean_dec(v_sz_2356_);
    v_i_boxed_2361_ = lean_unbox_usize(v_i_2357_);
    lean_dec(v_i_2357_);
    v_res_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_2354_, v_as_2355_, v_sz_boxed_2360_, v_i_boxed_2361_, v_b_2358_);
    lean_dec_ref(v_as_2355_);
    return v_res_2362_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0()
-> *mut LeanObject {
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2363_ = lean_box(0);
    v_dummy_2364_ = l_Lean_Expr_sort___override(v___x_2363_);
    return v_dummy_2364_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(
    mut v_e_2365_: *mut LeanObject,
    mut v_decl_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvars_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v_val_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2401_: usize = 0;
    let mut v___x_2402_: usize = 0;
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v_fst_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut v_a_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut v_a_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvars_2372_ = lean_ctor_get(v_decl_2366_, 0);
                v_mvarIdPending_2373_ = lean_ctor_get(v_decl_2366_, 1);
                v_isSharedCheck_2441_ = (!lean_is_exclusive(v_decl_2366_)) as u8;
                if v_isSharedCheck_2441_ == 0 {
                    v___x_2375_ = v_decl_2366_;
                    v_isShared_2376_ = v_isSharedCheck_2441_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mvarIdPending_2373_);
                    lean_inc(v_fvars_2372_);
                    lean_dec(v_decl_2366_);
                    v___x_2375_ = lean_box(0);
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
                    lean_dec(v___x_2377_);
                    lean_del_object(v___x_2375_);
                    lean_dec(v_mvarIdPending_2373_);
                    lean_dec_ref(v_fvars_2372_);
                    lean_dec_ref(v_e_2365_);
                    v___x_2380_ = lean_box((v___x_2379_) as usize);
                    v___x_2381_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2381_, 0, v___x_2380_);
                    return v___x_2381_;
                } else {
                    v___x_2382_ =
                        l_Lean_MVarId_findDecl_x3f___redArg(v_mvarIdPending_2373_, v_a_2368_);
                    lean_dec(v_mvarIdPending_2373_);
                    if lean_obj_tag(v___x_2382_) == 0 {
                        v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2432_ = (!lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2432_ == 0 {
                            v___x_2385_ = v___x_2382_;
                            v_isShared_2386_ = v_isSharedCheck_2432_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2383_);
                            lean_dec(v___x_2382_);
                            v___x_2385_ = lean_box(0);
                            v_isShared_2386_ = v_isSharedCheck_2432_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2377_);
                        lean_del_object(v___x_2375_);
                        lean_dec_ref(v_fvars_2372_);
                        lean_dec_ref(v_e_2365_);
                        v_a_2433_ = lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2440_ = (!lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2440_ == 0 {
                            v___x_2435_ = v___x_2382_;
                            v_isShared_2436_ = v_isSharedCheck_2440_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2433_);
                            lean_dec(v___x_2382_);
                            v___x_2435_ = lean_box(0);
                            v_isShared_2436_ = v_isSharedCheck_2440_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2383_) == 1 {
                    lean_del_object(v___x_2385_);
                    v_val_2387_ = lean_ctor_get(v_a_2383_, 0);
                    lean_inc(v_val_2387_);
                    lean_dec_ref_known(v_a_2383_, 1);
                    v___x_2388_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                    v_dummy_2389_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0_once), _init_l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment___closed__0);
                    lean_inc(v___x_2377_);
                    v___x_2390_ = lean_mk_array(v___x_2377_, v_dummy_2389_);
                    v___x_2391_ = lean_unsigned_to_nat(1);
                    v___x_2392_ = lean_nat_sub(v___x_2377_, v___x_2391_);
                    lean_dec(v___x_2377_);
                    v___x_2393_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_2365_,
                        v___x_2390_,
                        v___x_2392_,
                    );
                    v___x_2394_ = lean_unsigned_to_nat(0);
                    v___x_2395_ = lean_array_get_size(v___x_2393_);
                    v___x_2396_ =
                        l_Array_toSubarray___redArg(v___x_2393_, v___x_2394_, v___x_2395_);
                    v___x_2397_ = lean_box(0);
                    if v_isShared_2376_ == 0 {
                        lean_ctor_set(v___x_2375_, 1, v___x_2396_);
                        lean_ctor_set(v___x_2375_, 0, v___x_2388_);
                        v___x_2399_ = v___x_2375_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2388_);
                        lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2396_);
                        v___x_2399_ = v_reuseFailAlloc_2426_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2383_);
                    lean_dec(v___x_2377_);
                    lean_del_object(v___x_2375_);
                    lean_dec_ref(v_fvars_2372_);
                    lean_dec_ref(v_e_2365_);
                    v___x_2427_ = 0;
                    v___x_2428_ = lean_box((v___x_2427_) as usize);
                    if v_isShared_2386_ == 0 {
                        lean_ctor_set(v___x_2385_, 0, v___x_2428_);
                        v___x_2430_ = v___x_2385_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
                        v___x_2430_ = v_reuseFailAlloc_2431_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2400_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2400_, 0, v___x_2397_);
                lean_ctor_set(v___x_2400_, 1, v___x_2399_);
                v_sz_2401_ = lean_array_size(v_fvars_2372_);
                v___x_2402_ = 0usize;
                v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_2387_, v_fvars_2372_, v_sz_2401_, v___x_2402_, v___x_2400_);
                lean_dec_ref(v_fvars_2372_);
                if lean_obj_tag(v___x_2403_) == 0 {
                    v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
                    v_isSharedCheck_2417_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2406_ = v___x_2403_;
                        v_isShared_2407_ = v_isSharedCheck_2417_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2404_);
                        lean_dec(v___x_2403_);
                        v___x_2406_ = lean_box(0);
                        v_isShared_2407_ = v_isSharedCheck_2417_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2418_ = lean_ctor_get(v___x_2403_, 0);
                    v_isSharedCheck_2425_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                    if v_isSharedCheck_2425_ == 0 {
                        v___x_2420_ = v___x_2403_;
                        v_isShared_2421_ = v_isSharedCheck_2425_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2418_);
                        lean_dec(v___x_2403_);
                        v___x_2420_ = lean_box(0);
                        v_isShared_2421_ = v_isSharedCheck_2425_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2408_ = lean_ctor_get(v_a_2404_, 0);
                lean_inc(v_fst_2408_);
                lean_dec(v_a_2404_);
                if lean_obj_tag(v_fst_2408_) == 0 {
                    v___x_2409_ = lean_box((v___x_2379_) as usize);
                    if v_isShared_2407_ == 0 {
                        lean_ctor_set(v___x_2406_, 0, v___x_2409_);
                        v___x_2411_ = v___x_2406_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
                        v___x_2411_ = v_reuseFailAlloc_2412_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_2413_ = lean_ctor_get(v_fst_2408_, 0);
                    lean_inc(v_val_2413_);
                    lean_dec_ref_known(v_fst_2408_, 1);
                    if v_isShared_2407_ == 0 {
                        lean_ctor_set(v___x_2406_, 0, v_val_2413_);
                        v___x_2415_ = v___x_2406_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_val_2413_);
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
                    v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
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
                    v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
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
    mut v_e_2442_: *mut LeanObject,
    mut v_decl_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(
        v_e_2442_,
        v_decl_2443_,
        v_a_2444_,
        v_a_2445_,
        v_a_2446_,
        v_a_2447_,
    );
    lean_dec(v_a_2447_);
    lean_dec_ref(v_a_2446_);
    lean_dec(v_a_2445_);
    lean_dec_ref(v_a_2444_);
    return v_res_2449_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(
    mut v_00_u03b2_2450_: *mut LeanObject,
    mut v_m_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
) -> u8 {
    let mut v___x_2453_: u8 = 0;
    v___x_2453_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___redArg(v_m_2451_, v_a_2452_);
    return v___x_2453_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0___boxed(
    mut v_00_u03b2_2454_: *mut LeanObject,
    mut v_m_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2457_: u8 = 0;
    let mut v_r_2458_: *mut LeanObject = core::ptr::null_mut();
    v_res_2457_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0(v_00_u03b2_2454_, v_m_2455_, v_a_2456_);
    lean_dec(v_a_2456_);
    lean_dec_ref(v_m_2455_);
    v_r_2458_ = lean_box((v_res_2457_) as usize);
    return v_r_2458_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1(
    mut v_00_u03b2_2459_: *mut LeanObject,
    mut v_m_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
    mut v_b_2462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    v___x_2463_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1___redArg(v_m_2460_, v_a_2461_, v_b_2462_);
    return v___x_2463_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(
    mut v_val_2464_: *mut LeanObject,
    mut v_as_2465_: *mut LeanObject,
    mut v_sz_2466_: usize,
    mut v_i_2467_: usize,
    mut v_b_2468_: *mut LeanObject,
    mut v___y_2469_: *mut LeanObject,
    mut v___y_2470_: *mut LeanObject,
    mut v___y_2471_: *mut LeanObject,
    mut v___y_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___redArg(v_val_2464_, v_as_2465_, v_sz_2466_, v_i_2467_, v_b_2468_);
    return v___x_2474_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2___boxed(
    mut v_val_2475_: *mut LeanObject,
    mut v_as_2476_: *mut LeanObject,
    mut v_sz_2477_: *mut LeanObject,
    mut v_i_2478_: *mut LeanObject,
    mut v_b_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
    mut v___y_2482_: *mut LeanObject,
    mut v___y_2483_: *mut LeanObject,
    mut v___y_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2485_: usize = 0;
    let mut v_i_boxed_2486_: usize = 0;
    let mut v_res_2487_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2485_ = lean_unbox_usize(v_sz_2477_);
    lean_dec(v_sz_2477_);
    v_i_boxed_2486_ = lean_unbox_usize(v_i_2478_);
    lean_dec(v_i_2478_);
    v_res_2487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__2(v_val_2475_, v_as_2476_, v_sz_boxed_2485_, v_i_boxed_2486_, v_b_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
    lean_dec(v___y_2483_);
    lean_dec_ref(v___y_2482_);
    lean_dec(v___y_2481_);
    lean_dec_ref(v___y_2480_);
    lean_dec_ref(v_as_2476_);
    return v_res_2487_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(
    mut v_00_u03b2_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_x_2490_: *mut LeanObject,
) -> u8 {
    let mut v___x_2491_: u8 = 0;
    v___x_2491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___redArg(v_a_2489_, v_x_2490_);
    return v___x_2491_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0___boxed(
    mut v_00_u03b2_2492_: *mut LeanObject,
    mut v_a_2493_: *mut LeanObject,
    mut v_x_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2495_: u8 = 0;
    let mut v_r_2496_: *mut LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__0_spec__0(v_00_u03b2_2492_, v_a_2493_, v_x_2494_);
    lean_dec(v_x_2494_);
    lean_dec(v_a_2493_);
    v_r_2496_ = lean_box((v_res_2495_) as usize);
    return v_r_2496_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2(
    mut v_00_u03b2_2497_: *mut LeanObject,
    mut v_data_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    v___x_2499_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2___redArg(v_data_2498_);
    return v___x_2499_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2500_: *mut LeanObject,
    mut v_i_2501_: *mut LeanObject,
    mut v_source_2502_: *mut LeanObject,
    mut v_target_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    v___x_2504_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3___redArg(v_i_2501_, v_source_2502_, v_target_2503_);
    return v___x_2504_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_2505_: *mut LeanObject,
    mut v_x_2506_: *mut LeanObject,
    mut v_x_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment_spec__1_spec__2_spec__3_spec__5___redArg(v_x_2506_, v_x_2507_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(
    mut v_mvarId_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    v___x_2512_ = lean_st_ref_get(v___y_2510_);
    v_mctx_2513_ = lean_ctor_get(v___x_2512_, 0);
    lean_inc_ref(v_mctx_2513_);
    lean_dec(v___x_2512_);
    v___x_2514_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_2513_, v_mvarId_2509_);
    lean_dec_ref(v_mctx_2513_);
    v___x_2515_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2515_, 0, v___x_2514_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg___boxed(
    mut v_mvarId_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2519_: *mut LeanObject = core::ptr::null_mut();
    v_res_2519_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_2516_, v___y_2517_);
    lean_dec(v___y_2517_);
    lean_dec(v_mvarId_2516_);
    return v_res_2519_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(
    mut v_mvarId_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    v___x_2526_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarId_2520_, v___y_2522_);
    return v___x_2526_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___boxed(
    mut v_mvarId_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2533_: *mut LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0(v_mvarId_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
    lean_dec(v___y_2531_);
    lean_dec_ref(v___y_2530_);
    lean_dec(v___y_2529_);
    lean_dec_ref(v___y_2528_);
    lean_dec(v_mvarId_2527_);
    return v_res_2533_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(
    mut v_e_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut v_unused_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2537_ = l_Lean_Expr_hasMVar(v_e_2534_);
                if v___x_2537_ == 0 {
                    v___x_2538_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2538_, 0, v_e_2534_);
                    return v___x_2538_;
                } else {
                    v___x_2539_ = lean_st_ref_get(v___y_2535_);
                    v_mctx_2540_ = lean_ctor_get(v___x_2539_, 0);
                    lean_inc_ref(v_mctx_2540_);
                    lean_dec(v___x_2539_);
                    v___x_2541_ = l_Lean_instantiateMVarsCore(v_mctx_2540_, v_e_2534_);
                    v_fst_2542_ = lean_ctor_get(v___x_2541_, 0);
                    lean_inc(v_fst_2542_);
                    v_snd_2543_ = lean_ctor_get(v___x_2541_, 1);
                    lean_inc(v_snd_2543_);
                    lean_dec_ref(v___x_2541_);
                    v___x_2544_ = lean_st_ref_take(v___y_2535_);
                    v_cache_2545_ = lean_ctor_get(v___x_2544_, 1);
                    v_zetaDeltaFVarIds_2546_ = lean_ctor_get(v___x_2544_, 2);
                    v_postponed_2547_ = lean_ctor_get(v___x_2544_, 3);
                    v_diag_2548_ = lean_ctor_get(v___x_2544_, 4);
                    v_isSharedCheck_2557_ = (!lean_is_exclusive(v___x_2544_)) as u8;
                    if v_isSharedCheck_2557_ == 0 {
                        v_unused_2558_ = lean_ctor_get(v___x_2544_, 0);
                        lean_dec(v_unused_2558_);
                        v___x_2550_ = v___x_2544_;
                        v_isShared_2551_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2548_);
                        lean_inc(v_postponed_2547_);
                        lean_inc(v_zetaDeltaFVarIds_2546_);
                        lean_inc(v_cache_2545_);
                        lean_dec(v___x_2544_);
                        v___x_2550_ = lean_box(0);
                        v_isShared_2551_ = v_isSharedCheck_2557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2551_ == 0 {
                    lean_ctor_set(v___x_2550_, 0, v_snd_2543_);
                    v___x_2553_ = v___x_2550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_snd_2543_);
                    lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_cache_2545_);
                    lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_zetaDeltaFVarIds_2546_);
                    lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_postponed_2547_);
                    lean_ctor_set(v_reuseFailAlloc_2556_, 4, v_diag_2548_);
                    v___x_2553_ = v_reuseFailAlloc_2556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2554_ = lean_st_ref_set(v___y_2535_, v___x_2553_);
                v___x_2555_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2555_, 0, v_fst_2542_);
                return v___x_2555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg___boxed(
    mut v_e_2559_: *mut LeanObject,
    mut v___y_2560_: *mut LeanObject,
    mut v___y_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2562_: *mut LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_2559_, v___y_2560_);
    lean_dec(v___y_2560_);
    return v_res_2562_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(
    mut v_e_2563_: *mut LeanObject,
    mut v___y_2564_: *mut LeanObject,
    mut v___y_2565_: *mut LeanObject,
    mut v___y_2566_: *mut LeanObject,
    mut v___y_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    v___x_2569_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_e_2563_, v___y_2565_);
    return v___x_2569_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___boxed(
    mut v_e_2570_: *mut LeanObject,
    mut v___y_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
    mut v___y_2575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2576_: *mut LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1(v_e_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
    lean_dec(v___y_2574_);
    lean_dec_ref(v___y_2573_);
    lean_dec(v___y_2572_);
    lean_dec_ref(v___y_2571_);
    return v_res_2576_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(
    mut v_mvarId_2577_: *mut LeanObject,
    mut v___y_2578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    v___x_2580_ = lean_st_ref_get(v___y_2578_);
    v_mctx_2581_ = lean_ctor_get(v___x_2580_, 0);
    lean_inc_ref(v_mctx_2581_);
    lean_dec(v___x_2580_);
    v___x_2582_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_2581_, v_mvarId_2577_);
    lean_dec_ref(v_mctx_2581_);
    v___x_2583_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2583_, 0, v___x_2582_);
    return v___x_2583_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg___boxed(
    mut v_mvarId_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2587_: *mut LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_2584_, v___y_2585_);
    lean_dec(v___y_2585_);
    lean_dec(v_mvarId_2584_);
    return v_res_2587_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(
    mut v_mvarId_2588_: *mut LeanObject,
    mut v___y_2589_: *mut LeanObject,
    mut v___y_2590_: *mut LeanObject,
    mut v___y_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_2588_, v___y_2590_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___boxed(
    mut v_mvarId_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
    mut v___y_2598_: *mut LeanObject,
    mut v___y_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2601_: *mut LeanObject = core::ptr::null_mut();
    v_res_2601_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2(v_mvarId_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
    lean_dec(v___y_2599_);
    lean_dec_ref(v___y_2598_);
    lean_dec(v___y_2597_);
    lean_dec_ref(v___y_2596_);
    lean_dec(v_mvarId_2595_);
    return v_res_2601_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(
    mut v_mvarIdPending_2602_: *mut LeanObject,
    mut v_a_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v_val_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v_val_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_a_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v_a_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2668_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_a_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_a_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2608_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__0___redArg(v_mvarIdPending_2602_, v_a_2604_);
                if lean_obj_tag(v___x_2608_) == 0 {
                    v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
                    v_isSharedCheck_2684_ = (!lean_is_exclusive(v___x_2608_)) as u8;
                    if v_isSharedCheck_2684_ == 0 {
                        v___x_2611_ = v___x_2608_;
                        v_isShared_2612_ = v_isSharedCheck_2684_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2609_);
                        lean_dec(v___x_2608_);
                        v___x_2611_ = lean_box(0);
                        v_isShared_2612_ = v_isSharedCheck_2684_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarIdPending_2602_);
                    v_a_2685_ = lean_ctor_get(v___x_2608_, 0);
                    v_isSharedCheck_2692_ = (!lean_is_exclusive(v___x_2608_)) as u8;
                    if v_isSharedCheck_2692_ == 0 {
                        v___x_2687_ = v___x_2608_;
                        v_isShared_2688_ = v_isSharedCheck_2692_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_2685_);
                        lean_dec(v___x_2608_);
                        v___x_2687_ = lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2692_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2609_) == 1 {
                    v_val_2613_ = lean_ctor_get(v_a_2609_, 0);
                    lean_inc(v_val_2613_);
                    lean_dec_ref_known(v_a_2609_, 1);
                    v___x_2614_ = l_Lean_Expr_getAppFn_x27(v_val_2613_);
                    v___x_2615_ = l_Lean_Expr_isMVar(v___x_2614_);
                    lean_dec_ref(v___x_2614_);
                    if v___x_2615_ == 0 {
                        lean_dec(v_val_2613_);
                        if v_isShared_2612_ == 0 {
                            lean_ctor_set(v___x_2611_, 0, v_mvarIdPending_2602_);
                            v___x_2617_ = v___x_2611_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_mvarIdPending_2602_);
                            v___x_2617_ = v_reuseFailAlloc_2618_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2611_);
                        v___x_2619_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__1___redArg(v_val_2613_, v_a_2604_);
                        if lean_obj_tag(v___x_2619_) == 0 {
                            v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
                            v_isSharedCheck_2672_ = (!lean_is_exclusive(v___x_2619_)) as u8;
                            if v_isSharedCheck_2672_ == 0 {
                                v___x_2622_ = v___x_2619_;
                                v_isShared_2623_ = v_isSharedCheck_2672_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2620_);
                                lean_dec(v___x_2619_);
                                v___x_2622_ = lean_box(0);
                                v_isShared_2623_ = v_isSharedCheck_2672_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarIdPending_2602_);
                            v_a_2673_ = lean_ctor_get(v___x_2619_, 0);
                            v_isSharedCheck_2680_ = (!lean_is_exclusive(v___x_2619_)) as u8;
                            if v_isSharedCheck_2680_ == 0 {
                                v___x_2675_ = v___x_2619_;
                                v_isShared_2676_ = v_isSharedCheck_2680_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_2673_);
                                lean_dec(v___x_2619_);
                                v___x_2675_ = lean_box(0);
                                v_isShared_2676_ = v_isSharedCheck_2680_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_2609_);
                    if v_isShared_2612_ == 0 {
                        lean_ctor_set(v___x_2611_, 0, v_mvarIdPending_2602_);
                        v___x_2682_ = v___x_2611_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_mvarIdPending_2602_);
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
                lean_dec(v_a_2620_);
                if lean_obj_tag(v___x_2624_) == 2 {
                    lean_dec(v_mvarIdPending_2602_);
                    v_mvarId_2625_ = lean_ctor_get(v___x_2624_, 0);
                    lean_inc(v_mvarId_2625_);
                    lean_dec_ref_known(v___x_2624_, 1);
                    if v_isShared_2623_ == 0 {
                        lean_ctor_set(v___x_2622_, 0, v_mvarId_2625_);
                        v___x_2627_ = v___x_2622_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_mvarId_2625_);
                        v___x_2627_ = v_reuseFailAlloc_2628_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2629_ = l_Lean_Expr_getAppFn_x27(v___x_2624_);
                    if lean_obj_tag(v___x_2629_) == 2 {
                        lean_del_object(v___x_2622_);
                        v_mvarId_2630_ = lean_ctor_get(v___x_2629_, 0);
                        lean_inc(v_mvarId_2630_);
                        lean_dec_ref_known(v___x_2629_, 1);
                        v___x_2631_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_2630_, v_a_2604_);
                        lean_dec(v_mvarId_2630_);
                        if lean_obj_tag(v___x_2631_) == 0 {
                            v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
                            v_isSharedCheck_2660_ = (!lean_is_exclusive(v___x_2631_)) as u8;
                            if v_isSharedCheck_2660_ == 0 {
                                v___x_2634_ = v___x_2631_;
                                v_isShared_2635_ = v_isSharedCheck_2660_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2632_);
                                lean_dec(v___x_2631_);
                                v___x_2634_ = lean_box(0);
                                v_isShared_2635_ = v_isSharedCheck_2660_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_2624_);
                            lean_dec(v_mvarIdPending_2602_);
                            v_a_2661_ = lean_ctor_get(v___x_2631_, 0);
                            v_isSharedCheck_2668_ = (!lean_is_exclusive(v___x_2631_)) as u8;
                            if v_isSharedCheck_2668_ == 0 {
                                v___x_2663_ = v___x_2631_;
                                v_isShared_2664_ = v_isSharedCheck_2668_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_2661_);
                                lean_dec(v___x_2631_);
                                v___x_2663_ = lean_box(0);
                                v_isShared_2664_ = v_isSharedCheck_2668_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2629_);
                        lean_dec_ref(v___x_2624_);
                        if v_isShared_2623_ == 0 {
                            lean_ctor_set(v___x_2622_, 0, v_mvarIdPending_2602_);
                            v___x_2670_ = v___x_2622_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_mvarIdPending_2602_);
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
                if lean_obj_tag(v_a_2632_) == 1 {
                    lean_del_object(v___x_2634_);
                    v_val_2636_ = lean_ctor_get(v_a_2632_, 0);
                    lean_inc_n(v_val_2636_, 2);
                    lean_dec_ref_known(v_a_2632_, 1);
                    v___x_2637_ = l_Lean_PrettyPrinter_Delaborator_checkDelayedMVarAssignment(
                        v___x_2624_,
                        v_val_2636_,
                        v_a_2603_,
                        v_a_2604_,
                        v_a_2605_,
                        v_a_2606_,
                    );
                    if lean_obj_tag(v___x_2637_) == 0 {
                        v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
                        v_isSharedCheck_2648_ = (!lean_is_exclusive(v___x_2637_)) as u8;
                        if v_isSharedCheck_2648_ == 0 {
                            v___x_2640_ = v___x_2637_;
                            v_isShared_2641_ = v_isSharedCheck_2648_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2638_);
                            lean_dec(v___x_2637_);
                            v___x_2640_ = lean_box(0);
                            v_isShared_2641_ = v_isSharedCheck_2648_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2636_);
                        lean_dec(v_mvarIdPending_2602_);
                        v_a_2649_ = lean_ctor_get(v___x_2637_, 0);
                        v_isSharedCheck_2656_ = (!lean_is_exclusive(v___x_2637_)) as u8;
                        if v_isSharedCheck_2656_ == 0 {
                            v___x_2651_ = v___x_2637_;
                            v_isShared_2652_ = v_isSharedCheck_2656_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2649_);
                            lean_dec(v___x_2637_);
                            v___x_2651_ = lean_box(0);
                            v_isShared_2652_ = v_isSharedCheck_2656_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2632_);
                    lean_dec_ref(v___x_2624_);
                    if v_isShared_2635_ == 0 {
                        lean_ctor_set(v___x_2634_, 0, v_mvarIdPending_2602_);
                        v___x_2658_ = v___x_2634_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_mvarIdPending_2602_);
                        v___x_2658_ = v_reuseFailAlloc_2659_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2642_ = (lean_unbox(v_a_2638_) as u8);
                lean_dec(v_a_2638_);
                if v___x_2642_ == 0 {
                    lean_dec(v_val_2636_);
                    if v_isShared_2641_ == 0 {
                        lean_ctor_set(v___x_2640_, 0, v_mvarIdPending_2602_);
                        v___x_2644_ = v___x_2640_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_mvarIdPending_2602_);
                        v___x_2644_ = v_reuseFailAlloc_2645_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2640_);
                    lean_dec(v_mvarIdPending_2602_);
                    v_mvarIdPending_2646_ = lean_ctor_get(v_val_2636_, 1);
                    lean_inc(v_mvarIdPending_2646_);
                    lean_dec(v_val_2636_);
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
                    v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
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
                    v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
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
                    v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
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
                    v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
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
    mut v_mvarIdPending_2693_: *mut LeanObject,
    mut v_a_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2699_: *mut LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(
        v_mvarIdPending_2693_,
        v_a_2694_,
        v_a_2695_,
        v_a_2696_,
        v_a_2697_,
    );
    lean_dec(v_a_2697_);
    lean_dec_ref(v_a_2696_);
    lean_dec(v_a_2695_);
    lean_dec_ref(v_a_2694_);
    return v_res_2699_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(
    mut v_n_2701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    v___x_2702_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___closed__0;
    v___x_2703_ = lean_string_append(v___x_2702_, v_n_2701_);
    v___x_2704_ = lean_string_append(v___x_2703_, v___x_2702_);
    return v___x_2704_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap___boxed(
    mut v_n_2705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2706_: *mut LeanObject = core::ptr::null_mut();
    v_res_2706_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_n_2705_);
    lean_dec_ref(v_n_2705_);
    return v_res_2706_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___y_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: u8 = 0;
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2707_) == 0 {
                    v___x_2709_ = l_List_reverse___redArg(v_a_2708_);
                    return v___x_2709_;
                } else {
                    v_head_2710_ = lean_ctor_get(v_a_2707_, 0);
                    v_tail_2711_ = lean_ctor_get(v_a_2707_, 1);
                    v_isSharedCheck_2730_ = (!lean_is_exclusive(v_a_2707_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v___x_2713_ = v_a_2707_;
                        v_isShared_2714_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2711_);
                        lean_inc(v_head_2710_);
                        lean_dec(v_a_2707_);
                        v___x_2713_ = lean_box(0);
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
                    lean_dec_ref(v___x_2723_);
                    v___y_2716_ = v___x_2724_;
                    state = 2;
                    continue;
                } else {
                    v___x_2725_ = lean_erase_macro_scopes(v_head_2710_);
                    v___x_2726_ = l_Lean_Name_toString(v___x_2725_, v___x_2722_);
                    v___x_2727_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr___lam__0___closed__0;
                    v___x_2728_ = lean_string_append(v___x_2726_, v___x_2727_);
                    v___x_2729_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v___x_2728_);
                    lean_dec_ref(v___x_2728_);
                    v___y_2716_ = v___x_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2714_ == 0 {
                    lean_ctor_set(v___x_2713_, 1, v_a_2708_);
                    lean_ctor_set(v___x_2713_, 0, v___y_2716_);
                    v___x_2718_ = v___x_2713_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___y_2716_);
                    lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_a_2708_);
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
    mut v_ns_2732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0;
    v___x_2734_ = lean_box(0);
    v___x_2735_ = l_List_mapTR_loop___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString_spec__0(v_ns_2732_, v___x_2734_);
    v___x_2736_ = l_String_intercalate(v___x_2733_, v___x_2735_);
    return v___x_2736_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(
    mut v_count_2737_: *mut LeanObject,
    mut v_singular_2738_: *mut LeanObject,
    mut v_plural_2739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    v___x_2740_ = lean_unsigned_to_nat(1);
    v___x_2741_ = lean_nat_dec_eq(v_count_2737_, v___x_2740_);
    if v___x_2741_ == 0 {
        lean_inc_ref(v_plural_2739_);
        return v_plural_2739_;
    } else {
        lean_inc_ref(v_singular_2738_);
        return v_singular_2738_;
    }
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1___boxed(
    mut v_count_2742_: *mut LeanObject,
    mut v_singular_2743_: *mut LeanObject,
    mut v_plural_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2745_: *mut LeanObject = core::ptr::null_mut();
    v_res_2745_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v_count_2742_, v_singular_2743_, v_plural_2744_);
    lean_dec_ref(v_plural_2744_);
    lean_dec_ref(v_singular_2743_);
    lean_dec(v_count_2742_);
    return v_res_2745_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(
    mut v___x_2746_: *mut LeanObject,
    mut v_as_2747_: *mut LeanObject,
    mut v_i_2748_: usize,
    mut v_stop_2749_: usize,
    mut v_b_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_2753_: usize = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: u8 = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2751_ = lean_usize_dec_eq(v_i_2748_, v_stop_2749_);
                if v___x_2751_ == 0 {
                    v___x_2752_ = 1usize;
                    v___x_2753_ = lean_usize_sub(v_i_2748_, v___x_2752_);
                    v___x_2754_ = lean_array_uget_borrowed(v_as_2747_, v___x_2753_);
                    if lean_obj_tag(v___x_2754_) == 0 {
                        v_i_2748_ = v___x_2753_;
                        state = 0;
                        continue;
                    } else {
                        v_val_2756_ = lean_ctor_get(v___x_2754_, 0);
                        v___x_2757_ = l_Lean_LocalDecl_fvarId(v_val_2756_);
                        v___x_2758_ = l_Lean_LocalContext_contains(v___x_2746_, v___x_2757_);
                        lean_dec(v___x_2757_);
                        if v___x_2758_ == 0 {
                            v___x_2759_ = l_Lean_LocalDecl_userName(v_val_2756_);
                            v___x_2760_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_2760_, 0, v___x_2759_);
                            lean_ctor_set(v___x_2760_, 1, v_b_2750_);
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
    mut v___x_2763_: *mut LeanObject,
    mut v_as_2764_: *mut LeanObject,
    mut v_i_2765_: *mut LeanObject,
    mut v_stop_2766_: *mut LeanObject,
    mut v_b_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2768_: usize = 0;
    let mut v_stop_boxed_2769_: usize = 0;
    let mut v_res_2770_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2768_ = lean_unbox_usize(v_i_2765_);
    lean_dec(v_i_2765_);
    v_stop_boxed_2769_ = lean_unbox_usize(v_stop_2766_);
    lean_dec(v_stop_2766_);
    v_res_2770_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_2763_, v_as_2764_, v_i_boxed_2768_, v_stop_boxed_2769_, v_b_2767_);
    lean_dec_ref(v_as_2764_);
    lean_dec_ref(v___x_2763_);
    return v_res_2770_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(
    mut v___x_2771_: *mut LeanObject,
    mut v_x_2772_: *mut LeanObject,
    mut v_x_2773_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2772_) == 0 {
        let mut v_cs_2774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2777_: u8 = 0;
        v_cs_2774_ = lean_ctor_get(v_x_2772_, 0);
        v___x_2775_ = lean_array_get_size(v_cs_2774_);
        v___x_2776_ = lean_unsigned_to_nat(0);
        v___x_2777_ = lean_nat_dec_lt(v___x_2776_, v___x_2775_);
        if v___x_2777_ == 0 {
            return v_x_2773_;
        } else {
            let mut v___x_2778_: usize = 0;
            let mut v___x_2779_: usize = 0;
            let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
            v___x_2778_ = lean_usize_of_nat(v___x_2775_);
            v___x_2779_ = 0usize;
            v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_2771_, v_cs_2774_, v___x_2778_, v___x_2779_, v_x_2773_);
            return v___x_2780_;
        }
    } else {
        let mut v_vs_2781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2784_: u8 = 0;
        v_vs_2781_ = lean_ctor_get(v_x_2772_, 0);
        v___x_2782_ = lean_array_get_size(v_vs_2781_);
        v___x_2783_ = lean_unsigned_to_nat(0);
        v___x_2784_ = lean_nat_dec_lt(v___x_2783_, v___x_2782_);
        if v___x_2784_ == 0 {
            return v_x_2773_;
        } else {
            let mut v___x_2785_: usize = 0;
            let mut v___x_2786_: usize = 0;
            let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
            v___x_2785_ = lean_usize_of_nat(v___x_2782_);
            v___x_2786_ = 0usize;
            v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_2771_, v_vs_2781_, v___x_2785_, v___x_2786_, v_x_2773_);
            return v___x_2787_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(
    mut v___x_2788_: *mut LeanObject,
    mut v_as_2789_: *mut LeanObject,
    mut v_i_2790_: usize,
    mut v_stop_2791_: usize,
    mut v_b_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2794_: usize = 0;
    let mut v___x_2795_: usize = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_2799_: *mut LeanObject,
    mut v_as_2800_: *mut LeanObject,
    mut v_i_2801_: *mut LeanObject,
    mut v_stop_2802_: *mut LeanObject,
    mut v_b_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2804_: usize = 0;
    let mut v_stop_boxed_2805_: usize = 0;
    let mut v_res_2806_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2804_ = lean_unbox_usize(v_i_2801_);
    lean_dec(v_i_2801_);
    v_stop_boxed_2805_ = lean_unbox_usize(v_stop_2802_);
    lean_dec(v_stop_2802_);
    v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2_spec__3(v___x_2799_, v_as_2800_, v_i_boxed_2804_, v_stop_boxed_2805_, v_b_2803_);
    lean_dec_ref(v_as_2800_);
    lean_dec_ref(v___x_2799_);
    return v_res_2806_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2___boxed(
    mut v___x_2807_: *mut LeanObject,
    mut v_x_2808_: *mut LeanObject,
    mut v_x_2809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2810_: *mut LeanObject = core::ptr::null_mut();
    v_res_2810_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_2807_, v_x_2808_, v_x_2809_);
    lean_dec_ref(v_x_2808_);
    lean_dec_ref(v___x_2807_);
    return v_res_2810_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(
    mut v___x_2811_: *mut LeanObject,
    mut v_t_2812_: *mut LeanObject,
    mut v_init_2813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    v_root_2814_ = lean_ctor_get(v_t_2812_, 0);
    v_tail_2815_ = lean_ctor_get(v_t_2812_, 1);
    v___x_2816_ = lean_array_get_size(v_tail_2815_);
    v___x_2817_ = lean_unsigned_to_nat(0);
    v___x_2818_ = lean_nat_dec_lt(v___x_2817_, v___x_2816_);
    if v___x_2818_ == 0 {
        let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
        v___x_2819_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_2811_, v_root_2814_, v_init_2813_);
        return v___x_2819_;
    } else {
        let mut v___x_2820_: usize = 0;
        let mut v___x_2821_: usize = 0;
        let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
        v___x_2820_ = lean_usize_of_nat(v___x_2816_);
        v___x_2821_ = 0usize;
        v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__3(v___x_2811_, v_tail_2815_, v___x_2820_, v___x_2821_, v_init_2813_);
        v___x_2823_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0_spec__2(v___x_2811_, v_root_2814_, v___x_2822_);
        return v___x_2823_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0___boxed(
    mut v___x_2824_: *mut LeanObject,
    mut v_t_2825_: *mut LeanObject,
    mut v_init_2826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2827_: *mut LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_2824_, v_t_2825_, v_init_2826_);
    lean_dec_ref(v_t_2825_);
    lean_dec_ref(v___x_2824_);
    return v_res_2827_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(
    mut v___x_2828_: *mut LeanObject,
    mut v_lctx_2829_: *mut LeanObject,
    mut v_init_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    v_decls_2831_ = lean_ctor_get(v_lctx_2829_, 1);
    v___x_2832_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0_spec__0(v___x_2828_, v_decls_2831_, v_init_2830_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0___boxed(
    mut v___x_2833_: *mut LeanObject,
    mut v_lctx_2834_: *mut LeanObject,
    mut v_init_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2836_: *mut LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v___x_2833_, v_lctx_2834_, v_init_2835_);
    lean_dec_ref(v_lctx_2834_);
    lean_dec_ref(v___x_2833_);
    return v_res_2836_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(
    mut v_mdecl_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    v_lctx_2845_ = lean_ctor_get(v_a_2843_, 2);
    v_lctx_2846_ = lean_ctor_get(v_mdecl_2842_, 1);
    v___x_2847_ = lean_box(0);
    v___x_2848_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__0(v_lctx_2845_, v_lctx_2846_, v___x_2847_);
    v___x_2849_ = l_List_isEmpty___redArg(v___x_2848_);
    if v___x_2849_ == 0 {
        let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
        v___x_2850_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__0;
        v___x_2851_ = l_List_lengthTR___redArg(v___x_2848_);
        v___x_2852_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__1;
        v___x_2853_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__2;
        v___x_2854_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_2851_, v___x_2852_, v___x_2853_);
        lean_dec(v___x_2851_);
        v___x_2855_ = lean_string_append(v___x_2850_, v___x_2854_);
        lean_dec_ref(v___x_2854_);
        v___x_2856_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__3;
        v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
        v___x_2858_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_2848_);
        v___x_2859_ = lean_string_append(v___x_2857_, v___x_2858_);
        lean_dec_ref(v___x_2858_);
        v___x_2860_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2860_, 0, v___x_2859_);
        return v___x_2860_;
    } else {
        let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2848_);
        v___x_2861_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4;
        v___x_2862_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2862_, 0, v___x_2861_);
        return v___x_2862_;
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___boxed(
    mut v_mdecl_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2866_: *mut LeanObject = core::ptr::null_mut();
    v_res_2866_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_2863_, v_a_2864_);
    lean_dec_ref(v_a_2864_);
    lean_dec_ref(v_mdecl_2863_);
    return v_res_2866_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(
    mut v_mdecl_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
    mut v_a_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    v___x_2873_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_mdecl_2867_, v_a_2868_);
    return v___x_2873_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___boxed(
    mut v_mdecl_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
    mut v_a_2877_: *mut LeanObject,
    mut v_a_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2880_: *mut LeanObject = core::ptr::null_mut();
    v_res_2880_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars(v_mdecl_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
    lean_dec(v_a_2878_);
    lean_dec_ref(v_a_2877_);
    lean_dec(v_a_2876_);
    lean_dec_ref(v_a_2875_);
    lean_dec_ref(v_mdecl_2874_);
    return v_res_2880_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(
    mut v_lctxInitIndices_2881_: *mut LeanObject,
    mut v_mdecl_2882_: *mut LeanObject,
    mut v_as_2883_: *mut LeanObject,
    mut v_i_2884_: usize,
    mut v_stop_2885_: usize,
    mut v_b_2886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: usize = 0;
    let mut v___x_2889_: usize = 0;
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: u8 = 0;
    let mut v_lctx_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_2890_) == 0 {
                        v_i_2884_ = v___x_2889_;
                        state = 0;
                        continue;
                    } else {
                        v_val_2892_ = lean_ctor_get(v___x_2890_, 0);
                        v___x_2899_ = l_Lean_LocalDecl_index(v_val_2892_);
                        v___x_2900_ = lean_nat_dec_le(v_lctxInitIndices_2881_, v___x_2899_);
                        lean_dec(v___x_2899_);
                        if v___x_2900_ == 0 {
                            v_lctx_2901_ = lean_ctor_get(v_mdecl_2882_, 1);
                            v___x_2902_ = l_Lean_LocalDecl_fvarId(v_val_2892_);
                            v___x_2903_ = l_Lean_LocalContext_contains(v_lctx_2901_, v___x_2902_);
                            lean_dec(v___x_2902_);
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
                    v___x_2896_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2896_, 0, v___x_2895_);
                    lean_ctor_set(v___x_2896_, 1, v_b_2886_);
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
    mut v_lctxInitIndices_2904_: *mut LeanObject,
    mut v_mdecl_2905_: *mut LeanObject,
    mut v_as_2906_: *mut LeanObject,
    mut v_i_2907_: *mut LeanObject,
    mut v_stop_2908_: *mut LeanObject,
    mut v_b_2909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2910_: usize = 0;
    let mut v_stop_boxed_2911_: usize = 0;
    let mut v_res_2912_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2910_ = lean_unbox_usize(v_i_2907_);
    lean_dec(v_i_2907_);
    v_stop_boxed_2911_ = lean_unbox_usize(v_stop_2908_);
    lean_dec(v_stop_2908_);
    v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_2904_, v_mdecl_2905_, v_as_2906_, v_i_boxed_2910_, v_stop_boxed_2911_, v_b_2909_);
    lean_dec_ref(v_as_2906_);
    lean_dec_ref(v_mdecl_2905_);
    lean_dec(v_lctxInitIndices_2904_);
    return v_res_2912_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(
    mut v_lctxInitIndices_2913_: *mut LeanObject,
    mut v_mdecl_2914_: *mut LeanObject,
    mut v_x_2915_: *mut LeanObject,
    mut v_x_2916_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2915_) == 0 {
        let mut v_cs_2917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2920_: u8 = 0;
        v_cs_2917_ = lean_ctor_get(v_x_2915_, 0);
        v___x_2918_ = lean_array_get_size(v_cs_2917_);
        v___x_2919_ = lean_unsigned_to_nat(0);
        v___x_2920_ = lean_nat_dec_lt(v___x_2919_, v___x_2918_);
        if v___x_2920_ == 0 {
            return v_x_2916_;
        } else {
            let mut v___x_2921_: usize = 0;
            let mut v___x_2922_: usize = 0;
            let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
            v___x_2921_ = lean_usize_of_nat(v___x_2918_);
            v___x_2922_ = 0usize;
            v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_2913_, v_mdecl_2914_, v_cs_2917_, v___x_2921_, v___x_2922_, v_x_2916_);
            return v___x_2923_;
        }
    } else {
        let mut v_vs_2924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2927_: u8 = 0;
        v_vs_2924_ = lean_ctor_get(v_x_2915_, 0);
        v___x_2925_ = lean_array_get_size(v_vs_2924_);
        v___x_2926_ = lean_unsigned_to_nat(0);
        v___x_2927_ = lean_nat_dec_lt(v___x_2926_, v___x_2925_);
        if v___x_2927_ == 0 {
            return v_x_2916_;
        } else {
            let mut v___x_2928_: usize = 0;
            let mut v___x_2929_: usize = 0;
            let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
            v___x_2928_ = lean_usize_of_nat(v___x_2925_);
            v___x_2929_ = 0usize;
            v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_2913_, v_mdecl_2914_, v_vs_2924_, v___x_2928_, v___x_2929_, v_x_2916_);
            return v___x_2930_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(
    mut v_lctxInitIndices_2931_: *mut LeanObject,
    mut v_mdecl_2932_: *mut LeanObject,
    mut v_as_2933_: *mut LeanObject,
    mut v_i_2934_: usize,
    mut v_stop_2935_: usize,
    mut v_b_2936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: usize = 0;
    let mut v___x_2939_: usize = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_lctxInitIndices_2943_: *mut LeanObject,
    mut v_mdecl_2944_: *mut LeanObject,
    mut v_as_2945_: *mut LeanObject,
    mut v_i_2946_: *mut LeanObject,
    mut v_stop_2947_: *mut LeanObject,
    mut v_b_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2949_: usize = 0;
    let mut v_stop_boxed_2950_: usize = 0;
    let mut v_res_2951_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2949_ = lean_unbox_usize(v_i_2946_);
    lean_dec(v_i_2946_);
    v_stop_boxed_2950_ = lean_unbox_usize(v_stop_2947_);
    lean_dec(v_stop_2947_);
    v_res_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1_spec__2(v_lctxInitIndices_2943_, v_mdecl_2944_, v_as_2945_, v_i_boxed_2949_, v_stop_boxed_2950_, v_b_2948_);
    lean_dec_ref(v_as_2945_);
    lean_dec_ref(v_mdecl_2944_);
    lean_dec(v_lctxInitIndices_2943_);
    return v_res_2951_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1___boxed(
    mut v_lctxInitIndices_2952_: *mut LeanObject,
    mut v_mdecl_2953_: *mut LeanObject,
    mut v_x_2954_: *mut LeanObject,
    mut v_x_2955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2956_: *mut LeanObject = core::ptr::null_mut();
    v_res_2956_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_2952_, v_mdecl_2953_, v_x_2954_, v_x_2955_);
    lean_dec_ref(v_x_2954_);
    lean_dec_ref(v_mdecl_2953_);
    lean_dec(v_lctxInitIndices_2952_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(
    mut v_lctxInitIndices_2957_: *mut LeanObject,
    mut v_mdecl_2958_: *mut LeanObject,
    mut v_t_2959_: *mut LeanObject,
    mut v_init_2960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    v_root_2961_ = lean_ctor_get(v_t_2959_, 0);
    v_tail_2962_ = lean_ctor_get(v_t_2959_, 1);
    v___x_2963_ = lean_array_get_size(v_tail_2962_);
    v___x_2964_ = lean_unsigned_to_nat(0);
    v___x_2965_ = lean_nat_dec_lt(v___x_2964_, v___x_2963_);
    if v___x_2965_ == 0 {
        let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
        v___x_2966_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_2957_, v_mdecl_2958_, v_root_2961_, v_init_2960_);
        return v___x_2966_;
    } else {
        let mut v___x_2967_: usize = 0;
        let mut v___x_2968_: usize = 0;
        let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
        v___x_2967_ = lean_usize_of_nat(v___x_2963_);
        v___x_2968_ = 0usize;
        v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__2(v_lctxInitIndices_2957_, v_mdecl_2958_, v_tail_2962_, v___x_2967_, v___x_2968_, v_init_2960_);
        v___x_2970_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0_spec__1(v_lctxInitIndices_2957_, v_mdecl_2958_, v_root_2961_, v___x_2969_);
        return v___x_2970_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0___boxed(
    mut v_lctxInitIndices_2971_: *mut LeanObject,
    mut v_mdecl_2972_: *mut LeanObject,
    mut v_t_2973_: *mut LeanObject,
    mut v_init_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2975_: *mut LeanObject = core::ptr::null_mut();
    v_res_2975_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_2971_, v_mdecl_2972_, v_t_2973_, v_init_2974_);
    lean_dec_ref(v_t_2973_);
    lean_dec_ref(v_mdecl_2972_);
    lean_dec(v_lctxInitIndices_2971_);
    return v_res_2975_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(
    mut v_lctxInitIndices_2976_: *mut LeanObject,
    mut v_mdecl_2977_: *mut LeanObject,
    mut v_lctx_2978_: *mut LeanObject,
    mut v_init_2979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    v_decls_2980_ = lean_ctor_get(v_lctx_2978_, 1);
    v___x_2981_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0_spec__0(v_lctxInitIndices_2976_, v_mdecl_2977_, v_decls_2980_, v_init_2979_);
    return v___x_2981_;
}
pub unsafe fn l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0___boxed(
    mut v_lctxInitIndices_2982_: *mut LeanObject,
    mut v_mdecl_2983_: *mut LeanObject,
    mut v_lctx_2984_: *mut LeanObject,
    mut v_init_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2986_: *mut LeanObject = core::ptr::null_mut();
    v_res_2986_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_2982_, v_mdecl_2983_, v_lctx_2984_, v_init_2985_);
    lean_dec_ref(v_lctx_2984_);
    lean_dec_ref(v_mdecl_2983_);
    lean_dec(v_lctxInitIndices_2982_);
    return v_res_2986_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(
    mut v_lctxInitIndices_2991_: *mut LeanObject,
    mut v_mdecl_2992_: *mut LeanObject,
    mut v_a_2993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    v_lctx_2995_ = lean_ctor_get(v_a_2993_, 2);
    v___x_2996_ = lean_box(0);
    v___x_2997_ = l_Lean_LocalContext_foldrM___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars_spec__0(v_lctxInitIndices_2991_, v_mdecl_2992_, v_lctx_2995_, v___x_2996_);
    v___x_2998_ = l_List_isEmpty___redArg(v___x_2997_);
    if v___x_2998_ == 0 {
        let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
        v___x_2999_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__0;
        v___x_3000_ = l_List_lengthTR___redArg(v___x_2997_);
        v___x_3001_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__1;
        v___x_3002_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__2;
        v___x_3003_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars_spec__1(v___x_3000_, v___x_3001_, v___x_3002_);
        lean_dec(v___x_3000_);
        v___x_3004_ = lean_string_append(v___x_2999_, v___x_3003_);
        lean_dec_ref(v___x_3003_);
        v___x_3005_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___closed__3;
        v___x_3006_ = lean_string_append(v___x_3004_, v___x_3005_);
        v___x_3007_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString(v___x_2997_);
        v___x_3008_ = lean_string_append(v___x_3006_, v___x_3007_);
        lean_dec_ref(v___x_3007_);
        v___x_3009_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3009_, 0, v___x_3008_);
        return v___x_3009_;
    } else {
        let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2997_);
        v___x_3010_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4;
        v___x_3011_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3011_, 0, v___x_3010_);
        return v___x_3011_;
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg___boxed(
    mut v_lctxInitIndices_3012_: *mut LeanObject,
    mut v_mdecl_3013_: *mut LeanObject,
    mut v_a_3014_: *mut LeanObject,
    mut v_a_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3016_: *mut LeanObject = core::ptr::null_mut();
    v_res_3016_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_3012_, v_mdecl_3013_, v_a_3014_);
    lean_dec_ref(v_a_3014_);
    lean_dec_ref(v_mdecl_3013_);
    lean_dec(v_lctxInitIndices_3012_);
    return v_res_3016_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(
    mut v_lctxInitIndices_3017_: *mut LeanObject,
    mut v_mdecl_3018_: *mut LeanObject,
    mut v_a_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
    mut v_a_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    v___x_3024_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___redArg(v_lctxInitIndices_3017_, v_mdecl_3018_, v_a_3019_);
    return v___x_3024_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars___boxed(
    mut v_lctxInitIndices_3025_: *mut LeanObject,
    mut v_mdecl_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
    mut v_a_3029_: *mut LeanObject,
    mut v_a_3030_: *mut LeanObject,
    mut v_a_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3032_: *mut LeanObject = core::ptr::null_mut();
    v_res_3032_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_absentLCtxVars(v_lctxInitIndices_3025_, v_mdecl_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
    lean_dec(v_a_3030_);
    lean_dec_ref(v_a_3029_);
    lean_dec(v_a_3028_);
    lean_dec_ref(v_a_3027_);
    lean_dec_ref(v_mdecl_3026_);
    lean_dec(v_lctxInitIndices_3025_);
    return v_res_3032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(
    mut v_sz_3033_: usize,
    mut v_i_3034_: usize,
    mut v_bs_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: usize = 0;
    let mut v___x_3049_: usize = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3041_ = lean_usize_dec_lt(v_i_3034_, v_sz_3033_);
                if v___x_3041_ == 0 {
                    v___x_3042_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3042_, 0, v_bs_3035_);
                    return v___x_3042_;
                } else {
                    v_v_3043_ = lean_array_uget(v_bs_3035_, v_i_3034_);
                    v___x_3044_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3045_ = lean_array_uset(v_bs_3035_, v_i_3034_, v___x_3044_);
                    v___x_3052_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_v_3043_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
                    if lean_obj_tag(v___x_3052_) == 0 {
                        v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
                        lean_inc(v_a_3053_);
                        lean_dec_ref_known(v___x_3052_, 1);
                        v___x_3054_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_3053_);
                        lean_dec(v_a_3053_);
                        v_a_3047_ = v___x_3054_;
                        state = 1;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_3052_) == 0 {
                            v_a_3055_ = lean_ctor_get(v___x_3052_, 0);
                            lean_inc(v_a_3055_);
                            lean_dec_ref_known(v___x_3052_, 1);
                            v_a_3047_ = v_a_3055_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_bs_x27_3045_);
                            v_a_3056_ = lean_ctor_get(v___x_3052_, 0);
                            v_isSharedCheck_3063_ = (!lean_is_exclusive(v___x_3052_)) as u8;
                            if v_isSharedCheck_3063_ == 0 {
                                v___x_3058_ = v___x_3052_;
                                v_isShared_3059_ = v_isSharedCheck_3063_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3056_);
                                lean_dec(v___x_3052_);
                                v___x_3058_ = lean_box(0);
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
                    v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
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
    mut v_sz_3064_: *mut LeanObject,
    mut v_i_3065_: *mut LeanObject,
    mut v_bs_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
    mut v___y_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
    mut v___y_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3072_: usize = 0;
    let mut v_i_boxed_3073_: usize = 0;
    let mut v_res_3074_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3072_ = lean_unbox_usize(v_sz_3064_);
    lean_dec(v_sz_3064_);
    v_i_boxed_3073_ = lean_unbox_usize(v_i_3065_);
    lean_dec(v_i_3065_);
    v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_boxed_3072_, v_i_boxed_3073_, v_bs_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
    lean_dec(v___y_3070_);
    lean_dec_ref(v___y_3069_);
    lean_dec(v___y_3068_);
    lean_dec_ref(v___y_3067_);
    return v_res_3074_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(
    mut v___x_3077_: *mut LeanObject,
    mut v_as_3078_: *mut LeanObject,
    mut v_i_3079_: usize,
    mut v_stop_3080_: usize,
    mut v_b_3081_: *mut LeanObject,
    mut v___y_3082_: *mut LeanObject,
    mut v___y_3083_: *mut LeanObject,
    mut v___y_3084_: *mut LeanObject,
    mut v___y_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: usize = 0;
    let mut v___x_3090_: usize = 0;
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3103_: u8 = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3107_: u8 = 0;
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = lean_usize_dec_eq(v_i_3079_, v_stop_3080_);
                if v___x_3092_ == 0 {
                    v___x_3093_ = lean_array_uget_borrowed(v_as_3078_, v_i_3079_);
                    lean_inc(v___x_3093_);
                    v___x_3094_ = l_Lean_MVarId_getDecl(
                        v___x_3093_,
                        v___y_3082_,
                        v___y_3083_,
                        v___y_3084_,
                        v___y_3085_,
                    );
                    if lean_obj_tag(v___x_3094_) == 0 {
                        v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
                        lean_inc(v_a_3095_);
                        lean_dec_ref_known(v___x_3094_, 1);
                        v_lctx_3096_ = lean_ctor_get(v_a_3095_, 1);
                        lean_inc_ref(v_lctx_3096_);
                        lean_dec(v_a_3095_);
                        v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0;
                        v___x_3098_ = l_Lean_LocalContext_isSubPrefixOf(
                            v_lctx_3096_,
                            v___x_3077_,
                            v___x_3097_,
                        );
                        lean_dec_ref(v_lctx_3096_);
                        if v___x_3098_ == 0 {
                            lean_inc(v___x_3093_);
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
                        lean_dec_ref(v_b_3081_);
                        v_a_3100_ = lean_ctor_get(v___x_3094_, 0);
                        v_isSharedCheck_3107_ = (!lean_is_exclusive(v___x_3094_)) as u8;
                        if v_isSharedCheck_3107_ == 0 {
                            v___x_3102_ = v___x_3094_;
                            v_isShared_3103_ = v_isSharedCheck_3107_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3100_);
                            lean_dec(v___x_3094_);
                            v___x_3102_ = lean_box(0);
                            v_isShared_3103_ = v_isSharedCheck_3107_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3108_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3108_, 0, v_b_3081_);
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
                    v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
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
    mut v___x_3109_: *mut LeanObject,
    mut v_as_3110_: *mut LeanObject,
    mut v_i_3111_: *mut LeanObject,
    mut v_stop_3112_: *mut LeanObject,
    mut v_b_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
    mut v___y_3115_: *mut LeanObject,
    mut v___y_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3119_: usize = 0;
    let mut v_stop_boxed_3120_: usize = 0;
    let mut v_res_3121_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3119_ = lean_unbox_usize(v_i_3111_);
    lean_dec(v_i_3111_);
    v_stop_boxed_3120_ = lean_unbox_usize(v_stop_3112_);
    lean_dec(v_stop_3112_);
    v_res_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1(v___x_3109_, v_as_3110_, v_i_boxed_3119_, v_stop_boxed_3120_, v_b_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
    lean_dec(v___y_3117_);
    lean_dec_ref(v___y_3116_);
    lean_dec(v___y_3115_);
    lean_dec_ref(v___y_3114_);
    lean_dec_ref(v_as_3110_);
    lean_dec_ref(v___x_3109_);
    return v_res_3121_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(
    mut v_e_3128_: *mut LeanObject,
    mut v_a_3129_: *mut LeanObject,
    mut v_a_3130_: *mut LeanObject,
    mut v_a_3131_: *mut LeanObject,
    mut v_a_3132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_awaitingMVars_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: u8 = 0;
    let mut v_sz_3143_: usize = 0;
    let mut v___x_3144_: usize = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v_a_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u8 = 0;
    let mut v___y_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v_lctx_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: usize = 0;
    let mut v___x_3201_: usize = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: usize = 0;
    let mut v___x_3204_: usize = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3176_ = l_Lean_Meta_getMVarsNoDelayed(
                    v_e_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_,
                );
                if lean_obj_tag(v___x_3176_) == 0 {
                    v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
                    lean_inc(v_a_3177_);
                    lean_dec_ref_known(v___x_3176_, 1);
                    v___x_3194_ = lean_unsigned_to_nat(0);
                    v___x_3195_ = lean_array_get_size(v_a_3177_);
                    v___x_3196_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__4;
                    v___x_3197_ = lean_nat_dec_lt(v___x_3194_, v___x_3195_);
                    if v___x_3197_ == 0 {
                        v_a_3179_ = v___x_3196_;
                        state = 6;
                        continue;
                    } else {
                        v_lctx_3198_ = lean_ctor_get(v_a_3129_, 2);
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
                    v_a_3206_ = lean_ctor_get(v___x_3176_, 0);
                    v_isSharedCheck_3213_ = (!lean_is_exclusive(v___x_3176_)) as u8;
                    if v_isSharedCheck_3213_ == 0 {
                        v___x_3208_ = v___x_3176_;
                        v_isShared_3209_ = v_isSharedCheck_3213_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3206_);
                        lean_dec(v___x_3176_);
                        v___x_3208_ = lean_box(0);
                        v_isShared_3209_ = v_isSharedCheck_3213_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3140_ = lean_array_get_size(v_awaitingMVars_3135_);
                v___x_3141_ = lean_unsigned_to_nat(0);
                v___x_3142_ = lean_nat_dec_eq(v___x_3140_, v___x_3141_);
                if v___x_3142_ == 0 {
                    v_sz_3143_ = lean_array_size(v_awaitingMVars_3135_);
                    v___x_3144_ = 0usize;
                    v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__0(v_sz_3143_, v___x_3144_, v_awaitingMVars_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
                    if lean_obj_tag(v___x_3145_) == 0 {
                        v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
                        v_isSharedCheck_3165_ = (!lean_is_exclusive(v___x_3145_)) as u8;
                        if v_isSharedCheck_3165_ == 0 {
                            v___x_3148_ = v___x_3145_;
                            v_isShared_3149_ = v_isSharedCheck_3165_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3146_);
                            lean_dec(v___x_3145_);
                            v___x_3148_ = lean_box(0);
                            v_isShared_3149_ = v_isSharedCheck_3165_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3166_ = lean_ctor_get(v___x_3145_, 0);
                        v_isSharedCheck_3173_ = (!lean_is_exclusive(v___x_3145_)) as u8;
                        if v_isSharedCheck_3173_ == 0 {
                            v___x_3168_ = v___x_3145_;
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3166_);
                            lean_dec(v___x_3145_);
                            v___x_3168_ = lean_box(0);
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_awaitingMVars_3135_);
                    v___x_3174_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg___closed__4;
                    v___x_3175_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3175_, 0, v___x_3174_);
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
                lean_dec_ref(v___x_3154_);
                v___x_3156_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting___closed__3;
                v___x_3157_ = lean_string_append(v___x_3155_, v___x_3156_);
                v___x_3158_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_namesToString___closed__0;
                v___x_3159_ = lean_array_to_list(v_a_3146_);
                v___x_3160_ = l_String_intercalate(v___x_3158_, v___x_3159_);
                v___x_3161_ = lean_string_append(v___x_3157_, v___x_3160_);
                lean_dec_ref(v___x_3160_);
                if v_isShared_3149_ == 0 {
                    lean_ctor_set(v___x_3148_, 0, v___x_3161_);
                    v___x_3163_ = v___x_3148_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
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
                    v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
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
                v___x_3181_ = lean_unsigned_to_nat(0);
                v___x_3182_ = lean_nat_dec_eq(v___x_3180_, v___x_3181_);
                if v___x_3182_ == 0 {
                    lean_dec(v_a_3177_);
                    v_awaitingMVars_3135_ = v_a_3179_;
                    v___y_3136_ = v_a_3129_;
                    v___y_3137_ = v_a_3130_;
                    v___y_3138_ = v_a_3131_;
                    v___y_3139_ = v_a_3132_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_a_3179_);
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
                if lean_obj_tag(v___y_3184_) == 0 {
                    v_a_3185_ = lean_ctor_get(v___y_3184_, 0);
                    lean_inc(v_a_3185_);
                    lean_dec_ref_known(v___y_3184_, 1);
                    v_a_3179_ = v_a_3185_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_a_3177_);
                    v_a_3186_ = lean_ctor_get(v___y_3184_, 0);
                    v_isSharedCheck_3193_ = (!lean_is_exclusive(v___y_3184_)) as u8;
                    if v_isSharedCheck_3193_ == 0 {
                        v___x_3188_ = v___y_3184_;
                        v_isShared_3189_ = v_isSharedCheck_3193_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3186_);
                        lean_dec(v___y_3184_);
                        v___x_3188_ = lean_box(0);
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
                    v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
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
                    v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
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
    mut v_e_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
    mut v_a_3216_: *mut LeanObject,
    mut v_a_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3220_: *mut LeanObject = core::ptr::null_mut();
    v_res_3220_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_e_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
    lean_dec(v_a_3218_);
    lean_dec_ref(v_a_3217_);
    lean_dec(v_a_3216_);
    lean_dec_ref(v_a_3215_);
    return v_res_3220_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(
    mut v_mvarId_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    v___x_3224_ = lean_st_ref_get(v___y_3222_);
    v_mctx_3225_ = lean_ctor_get(v___x_3224_, 0);
    lean_inc_ref(v_mctx_3225_);
    lean_dec(v___x_3224_);
    v_decl_3226_ = l_Lean_MetavarContext_getDecl(v_mctx_3225_, v_mvarId_3221_);
    v_depth_3227_ = lean_ctor_get(v_decl_3226_, 3);
    lean_inc(v_depth_3227_);
    lean_dec_ref(v_decl_3226_);
    v_depth_3228_ = lean_ctor_get(v_mctx_3225_, 0);
    lean_inc(v_depth_3228_);
    lean_dec_ref(v_mctx_3225_);
    v___x_3229_ = lean_nat_dec_eq(v_depth_3227_, v_depth_3228_);
    lean_dec(v_depth_3228_);
    lean_dec(v_depth_3227_);
    v___x_3230_ = lean_box((v___x_3229_) as usize);
    v___x_3231_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3231_, 0, v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg___boxed(
    mut v_mvarId_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3235_: *mut LeanObject = core::ptr::null_mut();
    v_res_3235_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_3232_, v___y_3233_);
    lean_dec(v___y_3233_);
    return v_res_3235_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(
    mut v_mvarId_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_3236_, v___y_3238_);
    return v___x_3242_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___boxed(
    mut v_mvarId_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3249_: *mut LeanObject = core::ptr::null_mut();
    v_res_3249_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0(v_mvarId_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
    lean_dec(v___y_3247_);
    lean_dec_ref(v___y_3246_);
    lean_dec(v___y_3245_);
    lean_dec_ref(v___y_3244_);
    return v_res_3249_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(
    mut v_mvarId_3263_: *mut LeanObject,
    mut v_lctxInitIndices_3264_: *mut LeanObject,
    mut v_fromDelayed_3265_: u8,
    mut v_a_3266_: *mut LeanObject,
    mut v_a_3267_: *mut LeanObject,
    mut v_a_3268_: *mut LeanObject,
    mut v_a_3269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v_val_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v___y_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_delayedExpl_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v_val_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v_a_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v_a_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3348_: u8 = 0;
    let mut v_a_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3352_: u8 = 0;
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3356_: u8 = 0;
    let mut v_userName_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3359_: u8 = 0;
    let mut v_msg_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v_msg_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3407_: u8 = 0;
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v_mctx_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: u8 = 0;
    let mut v_reuseFailAlloc_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_a_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3271_ = l_Lean_MVarId_findDecl_x3f___redArg(v_mvarId_3263_, v_a_3267_);
                if lean_obj_tag(v___x_3271_) == 0 {
                    v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
                    v_isSharedCheck_3432_ = (!lean_is_exclusive(v___x_3271_)) as u8;
                    if v_isSharedCheck_3432_ == 0 {
                        v___x_3274_ = v___x_3271_;
                        v_isShared_3275_ = v_isSharedCheck_3432_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3272_);
                        lean_dec(v___x_3271_);
                        v___x_3274_ = lean_box(0);
                        v_isShared_3275_ = v_isSharedCheck_3432_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_3263_);
                    v_a_3433_ = lean_ctor_get(v___x_3271_, 0);
                    v_isSharedCheck_3440_ = (!lean_is_exclusive(v___x_3271_)) as u8;
                    if v_isSharedCheck_3440_ == 0 {
                        v___x_3435_ = v___x_3271_;
                        v_isShared_3436_ = v_isSharedCheck_3440_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_3433_);
                        lean_dec(v___x_3271_);
                        v___x_3435_ = lean_box(0);
                        v_isShared_3436_ = v_isSharedCheck_3440_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3272_) == 1 {
                    lean_del_object(v___x_3274_);
                    v_val_3276_ = lean_ctor_get(v_a_3272_, 0);
                    v_isSharedCheck_3427_ = (!lean_is_exclusive(v_a_3272_)) as u8;
                    if v_isSharedCheck_3427_ == 0 {
                        v___x_3278_ = v_a_3272_;
                        v_isShared_3279_ = v_isSharedCheck_3427_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3276_);
                        lean_dec(v_a_3272_);
                        v___x_3278_ = lean_box(0);
                        v_isShared_3279_ = v_isSharedCheck_3427_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3272_);
                    lean_dec(v_mvarId_3263_);
                    v___x_3428_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__12;
                    if v_isShared_3275_ == 0 {
                        lean_ctor_set(v___x_3274_, 0, v___x_3428_);
                        v___x_3430_ = v___x_3274_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
                        v___x_3430_ = v_reuseFailAlloc_3431_;
                        state = 23;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3293_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending_spec__2___redArg(v_mvarId_3263_, v_a_3267_);
                v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
                lean_inc(v_a_3294_);
                lean_dec_ref(v___x_3293_);
                v_delayedExpl_3295_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__0;
                if lean_obj_tag(v_a_3294_) == 1 {
                    lean_del_object(v___x_3278_);
                    lean_dec(v_val_3276_);
                    lean_dec(v_mvarId_3263_);
                    v_val_3296_ = lean_ctor_get(v_a_3294_, 0);
                    lean_inc(v_val_3296_);
                    lean_dec_ref_known(v_a_3294_, 1);
                    v_mvarIdPending_3297_ = lean_ctor_get(v_val_3296_, 1);
                    lean_inc(v_mvarIdPending_3297_);
                    lean_dec(v_val_3296_);
                    v___x_3298_ = l_Lean_PrettyPrinter_Delaborator_getDelayedMVarIdPending(
                        v_mvarIdPending_3297_,
                        v_a_3266_,
                        v_a_3267_,
                        v_a_3268_,
                        v_a_3269_,
                    );
                    if lean_obj_tag(v___x_3298_) == 0 {
                        v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
                        lean_inc(v_a_3299_);
                        lean_dec_ref_known(v___x_3298_, 1);
                        v___x_3300_ = l_Lean_MVarId_findDecl_x3f___redArg(v_a_3299_, v_a_3267_);
                        if lean_obj_tag(v___x_3300_) == 0 {
                            v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
                            v_isSharedCheck_3340_ = (!lean_is_exclusive(v___x_3300_)) as u8;
                            if v_isSharedCheck_3340_ == 0 {
                                v___x_3303_ = v___x_3300_;
                                v_isShared_3304_ = v_isSharedCheck_3340_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3301_);
                                lean_dec(v___x_3300_);
                                v___x_3303_ = lean_box(0);
                                v_isShared_3304_ = v_isSharedCheck_3340_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3299_);
                            v_a_3341_ = lean_ctor_get(v___x_3300_, 0);
                            v_isSharedCheck_3348_ = (!lean_is_exclusive(v___x_3300_)) as u8;
                            if v_isSharedCheck_3348_ == 0 {
                                v___x_3343_ = v___x_3300_;
                                v_isShared_3344_ = v_isSharedCheck_3348_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_3341_);
                                lean_dec(v___x_3300_);
                                v___x_3343_ = lean_box(0);
                                v_isShared_3344_ = v_isSharedCheck_3348_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        v_a_3349_ = lean_ctor_get(v___x_3298_, 0);
                        v_isSharedCheck_3356_ = (!lean_is_exclusive(v___x_3298_)) as u8;
                        if v_isSharedCheck_3356_ == 0 {
                            v___x_3351_ = v___x_3298_;
                            v_isShared_3352_ = v_isSharedCheck_3356_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3349_);
                            lean_dec(v___x_3298_);
                            v___x_3351_ = lean_box(0);
                            v_isShared_3352_ = v_isSharedCheck_3356_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3294_);
                    v_userName_3357_ = lean_ctor_get(v_val_3276_, 0);
                    v_lctx_3358_ = lean_ctor_get(v_val_3276_, 1);
                    v_kind_3359_ = lean_ctor_get_uint8(
                        v_val_3276_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
                lean_dec(v_val_3276_);
                v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
                v_isSharedCheck_3292_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                if v_isSharedCheck_3292_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    v_isShared_3287_ = v_isSharedCheck_3292_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_a_3284_);
                    lean_dec(v___x_3283_);
                    v___x_3286_ = lean_box(0);
                    v_isShared_3287_ = v_isSharedCheck_3292_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3288_ = lean_string_append(v___y_3282_, v_a_3284_);
                lean_dec(v_a_3284_);
                if v_isShared_3287_ == 0 {
                    lean_ctor_set(v___x_3286_, 0, v___x_3288_);
                    v___x_3290_ = v___x_3286_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
                    v___x_3290_ = v_reuseFailAlloc_3291_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3290_;
            }
            6 => {
                if lean_obj_tag(v_a_3301_) == 1 {
                    lean_del_object(v___x_3303_);
                    v_val_3305_ = lean_ctor_get(v_a_3301_, 0);
                    lean_inc(v_val_3305_);
                    lean_dec_ref_known(v_a_3301_, 1);
                    lean_inc(v_a_3299_);
                    v___x_3332_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAsStr(v_a_3299_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
                    if lean_obj_tag(v___x_3332_) == 0 {
                        v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
                        lean_inc(v_a_3333_);
                        lean_dec_ref_known(v___x_3332_, 1);
                        v___x_3334_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_wrap(v_a_3333_);
                        lean_dec(v_a_3333_);
                        v_a_3320_ = v___x_3334_;
                        state = 10;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_3332_) == 0 {
                            v_a_3335_ = lean_ctor_get(v___x_3332_, 0);
                            lean_inc(v_a_3335_);
                            lean_dec_ref_known(v___x_3332_, 1);
                            v_a_3320_ = v_a_3335_;
                            state = 10;
                            continue;
                        } else {
                            lean_dec(v_val_3305_);
                            lean_dec(v_a_3299_);
                            return v___x_3332_;
                        }
                    }
                } else {
                    lean_dec(v_a_3301_);
                    lean_dec(v_a_3299_);
                    v___x_3336_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__3;
                    if v_isShared_3304_ == 0 {
                        lean_ctor_set(v___x_3303_, 0, v___x_3336_);
                        v___x_3338_ = v___x_3303_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
                        v___x_3338_ = v_reuseFailAlloc_3339_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3309_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_3305_, v___y_3308_);
                lean_dec(v_val_3305_);
                v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
                v_isSharedCheck_3318_ = (!lean_is_exclusive(v___x_3309_)) as u8;
                if v_isSharedCheck_3318_ == 0 {
                    v___x_3312_ = v___x_3309_;
                    v_isShared_3313_ = v_isSharedCheck_3318_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_a_3310_);
                    lean_dec(v___x_3309_);
                    v___x_3312_ = lean_box(0);
                    v_isShared_3313_ = v_isSharedCheck_3318_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3314_ = lean_string_append(v_msg_3307_, v_a_3310_);
                lean_dec(v_a_3310_);
                if v_isShared_3313_ == 0 {
                    lean_ctor_set(v___x_3312_, 0, v___x_3314_);
                    v___x_3316_ = v___x_3312_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
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
                lean_dec(v_a_3299_);
                v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
                lean_inc(v_a_3322_);
                lean_dec_ref(v___x_3321_);
                v___x_3323_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__1;
                v___x_3324_ = lean_string_append(v___x_3323_, v_a_3320_);
                lean_dec_ref(v_a_3320_);
                v___x_3325_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__2;
                v___x_3326_ = lean_string_append(v___x_3324_, v___x_3325_);
                v___x_3327_ = lean_string_append(v___x_3326_, v_delayedExpl_3295_);
                if lean_obj_tag(v_a_3322_) == 1 {
                    v_val_3328_ = lean_ctor_get(v_a_3322_, 0);
                    lean_inc(v_val_3328_);
                    lean_dec_ref_known(v_a_3322_, 1);
                    v___x_3329_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_3328_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
                    if lean_obj_tag(v___x_3329_) == 0 {
                        v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
                        lean_inc(v_a_3330_);
                        lean_dec_ref_known(v___x_3329_, 1);
                        v___x_3331_ = lean_string_append(v___x_3327_, v_a_3330_);
                        lean_dec(v_a_3330_);
                        v_msg_3307_ = v___x_3331_;
                        v___y_3308_ = v_a_3266_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec_ref(v___x_3327_);
                        lean_dec(v_val_3305_);
                        return v___x_3329_;
                    }
                } else {
                    lean_dec(v_a_3322_);
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
                    v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
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
                    v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
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
                    v_lctx_3363_ = lean_ctor_get(v___y_3362_, 2);
                    v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting_spec__1___closed__0;
                    v___x_3365_ =
                        l_Lean_LocalContext_isSubPrefixOf(v_lctx_3358_, v_lctx_3363_, v___x_3364_);
                    if v___x_3365_ == 0 {
                        v___x_3366_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_extraLCtxVars___redArg(v_val_3276_, v___y_3362_);
                        lean_dec(v_val_3276_);
                        v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
                        v_isSharedCheck_3375_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                        if v_isSharedCheck_3375_ == 0 {
                            v___x_3369_ = v___x_3366_;
                            v_isShared_3370_ = v_isSharedCheck_3375_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3367_);
                            lean_dec(v___x_3366_);
                            v___x_3369_ = lean_box(0);
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
                lean_dec(v_a_3367_);
                if v_isShared_3370_ == 0 {
                    lean_ctor_set(v___x_3369_, 0, v___x_3371_);
                    v___x_3373_ = v___x_3369_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
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
                v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
                lean_inc(v_a_3383_);
                lean_dec_ref(v___x_3382_);
                if lean_obj_tag(v_a_3383_) == 1 {
                    lean_dec(v_mvarId_3263_);
                    if v_fromDelayed_3265_ == 0 {
                        lean_dec_ref_known(v_a_3383_, 1);
                        v___x_3384_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__4;
                        v___x_3385_ = lean_string_append(v_msg_3377_, v___x_3384_);
                        v_msg_3361_ = v___x_3385_;
                        v___y_3362_ = v___y_3378_;
                        state = 16;
                        continue;
                    } else {
                        v_val_3386_ = lean_ctor_get(v_a_3383_, 0);
                        lean_inc(v_val_3386_);
                        lean_dec_ref_known(v_a_3383_, 1);
                        v___x_3387_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_collectAwaiting(v_val_3386_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
                        if lean_obj_tag(v___x_3387_) == 0 {
                            v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
                            lean_inc(v_a_3388_);
                            lean_dec_ref_known(v___x_3387_, 1);
                            v___x_3389_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___closed__5;
                            v___x_3390_ = lean_string_append(v_msg_3377_, v___x_3389_);
                            v___x_3391_ = lean_string_append(v___x_3390_, v_delayedExpl_3295_);
                            v___x_3392_ = lean_string_append(v___x_3391_, v_a_3388_);
                            lean_dec(v_a_3388_);
                            v_msg_3361_ = v___x_3392_;
                            v___y_3362_ = v___y_3378_;
                            state = 16;
                            continue;
                        } else {
                            lean_dec_ref(v_msg_3377_);
                            lean_dec(v_val_3276_);
                            return v___x_3387_;
                        }
                    }
                } else {
                    lean_dec(v_a_3383_);
                    v___x_3393_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar_spec__0___redArg(v_mvarId_3263_, v___y_3379_);
                    v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
                    lean_inc(v_a_3394_);
                    lean_dec_ref(v___x_3393_);
                    v___x_3395_ = (lean_unbox(v_a_3394_) as u8);
                    lean_dec(v_a_3394_);
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
                    lean_inc_ref(v___y_3402_);
                    v___x_3409_ = lean_string_append(v___y_3402_, v___x_3408_);
                    v_msg_3377_ = v___x_3409_;
                    v___y_3378_ = v___y_3406_;
                    v___y_3379_ = v___y_3403_;
                    v___y_3380_ = v___y_3405_;
                    v___y_3381_ = v___y_3404_;
                    state = 19;
                    continue;
                } else {
                    lean_inc_ref(v___y_3402_);
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
                    v_mctx_3418_ = lean_ctor_get(v___x_3416_, 0);
                    lean_inc_ref(v_mctx_3418_);
                    lean_dec(v___x_3416_);
                    lean_inc(v_mvarId_3263_);
                    if v_isShared_3279_ == 0 {
                        lean_ctor_set(v___x_3278_, 0, v_mvarId_3263_);
                        v___x_3420_ = v___x_3278_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_mvarId_3263_);
                        v___x_3420_ = v_reuseFailAlloc_3423_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3416_);
                    lean_del_object(v___x_3278_);
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
                lean_dec_ref(v_mctx_3418_);
                v___x_3422_ = l_Option_instBEq_beq___at___00__private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_delabMVarAuxAux_spec__0(v___x_3420_, v___x_3421_);
                lean_dec(v___x_3421_);
                lean_dec_ref(v___x_3420_);
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
                    v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
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
    mut v_mvarId_3441_: *mut LeanObject,
    mut v_lctxInitIndices_3442_: *mut LeanObject,
    mut v_fromDelayed_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fromDelayed_boxed_3449_: u8 = 0;
    let mut v_res_3450_: *mut LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3449_ = (lean_unbox(v_fromDelayed_3443_) as u8);
    v_res_3450_ = l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar(v_mvarId_3441_, v_lctxInitIndices_3442_, v_fromDelayed_boxed_3449_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
    lean_dec(v_a_3447_);
    lean_dec_ref(v_a_3446_);
    lean_dec(v_a_3445_);
    lean_dec_ref(v_a_3444_);
    lean_dec(v_lctxInitIndices_3442_);
    return v_res_3450_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(
    mut v_mvarId_3451_: *mut LeanObject,
    mut v_lctxInitIndices_3452_: *mut LeanObject,
    mut v_fromDelayed_3453_: u8,
    mut v_ppCtx_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    v___x_3456_ = lean_box((v_fromDelayed_3453_) as usize);
    v___x_3457_ = lean_alloc_closure(l___private_Lean_PrettyPrinter_Delaborator_Metavariable_0__Lean_PrettyPrinter_Delaborator_describeMVar___boxed as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_3457_, 0, v_mvarId_3451_);
    lean_closure_set(v___x_3457_, 1, v_lctxInitIndices_3452_);
    lean_closure_set(v___x_3457_, 2, v___x_3456_);
    v___x_3458_ = l_Lean_PPContext_runMetaM___redArg(v_ppCtx_3454_, v___x_3457_);
    return v___x_3458_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed(
    mut v_mvarId_3459_: *mut LeanObject,
    mut v_lctxInitIndices_3460_: *mut LeanObject,
    mut v_fromDelayed_3461_: *mut LeanObject,
    mut v_ppCtx_3462_: *mut LeanObject,
    mut v___y_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fromDelayed_boxed_3464_: u8 = 0;
    let mut v_res_3465_: *mut LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3464_ = (lean_unbox(v_fromDelayed_3461_) as u8);
    v_res_3465_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0(
        v_mvarId_3459_,
        v_lctxInitIndices_3460_,
        v_fromDelayed_boxed_3464_,
        v_ppCtx_3462_,
    );
    lean_dec_ref(v_ppCtx_3462_);
    return v_res_3465_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(
    mut v_mvarId_3466_: *mut LeanObject,
    mut v_fromDelayed_3467_: u8,
    mut v_a_3468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctxInitIndices_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    v_lctxInitIndices_3470_ = lean_ctor_get(v_a_3468_, 5);
    v___x_3471_ = lean_box((v_fromDelayed_3467_) as usize);
    lean_inc(v_lctxInitIndices_3470_);
    v___f_3472_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3472_, 0, v_mvarId_3466_);
    lean_closure_set(v___f_3472_, 1, v_lctxInitIndices_3470_);
    lean_closure_set(v___f_3472_, 2, v___x_3471_);
    v___x_3473_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3473_, 0, v___f_3472_);
    return v___x_3473_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg___boxed(
    mut v_mvarId_3474_: *mut LeanObject,
    mut v_fromDelayed_3475_: *mut LeanObject,
    mut v_a_3476_: *mut LeanObject,
    mut v_a_3477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fromDelayed_boxed_3478_: u8 = 0;
    let mut v_res_3479_: *mut LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3478_ = (lean_unbox(v_fromDelayed_3475_) as u8);
    v_res_3479_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(
        v_mvarId_3474_,
        v_fromDelayed_boxed_3478_,
        v_a_3476_,
    );
    lean_dec_ref(v_a_3476_);
    return v_res_3479_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar(
    mut v_mvarId_3480_: *mut LeanObject,
    mut v_fromDelayed_3481_: u8,
    mut v_a_3482_: *mut LeanObject,
    mut v_a_3483_: *mut LeanObject,
    mut v_a_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
    mut v_a_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    v___x_3489_ = l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___redArg(
        v_mvarId_3480_,
        v_fromDelayed_3481_,
        v_a_3482_,
    );
    return v___x_3489_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_mkDescribeMVar___boxed(
    mut v_mvarId_3490_: *mut LeanObject,
    mut v_fromDelayed_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fromDelayed_boxed_3499_: u8 = 0;
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_fromDelayed_boxed_3499_ = (lean_unbox(v_fromDelayed_3491_) as u8);
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
    lean_dec(v_a_3497_);
    lean_dec_ref(v_a_3496_);
    lean_dec(v_a_3495_);
    lean_dec_ref(v_a_3494_);
    lean_dec(v_a_3493_);
    lean_dec_ref(v_a_3492_);
    return v_res_3500_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_Metavariable(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ErrorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_Metavariable(builtin);
}
